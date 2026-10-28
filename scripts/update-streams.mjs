// Denné obnovenie ponuky streamov (spúšťa GitHub Actions, funguje aj ručne: node scripts/update-streams.mjs)
//
//  1. načíta seeds.json (tvoj kurátorovaný zoznam staníc a ich známych adries)
//  2. spýta sa databázy radio-browser.info na slovenské stanice + hľadá aj pre každú stanicu zo seeds.json
//  3. každú kandidátsku adresu SKUTOČNE otvorí a overí, že tečie zvuk (aj staré Shoutcast "ICY 200 OK" streamy)
//  4. adresy zoradí od najvyššieho bitrate (primárny) po nižšie (sekundárne), HTTPS pred HTTP
//  5. nové stanice dá do skupiny „new“; do hlavnej ponuky sa dostanú až po PROMOTE_AFTER rôznych dňoch úspešnej kontroly
//  6. zapíše streams.json (len ak sa obsah zmenil)
//
// Poistky: nič sa z kurátorovaného zoznamu nikdy nemaže; ak je sieť/API nedostupné, starý streams.json ostane.

import fs from 'node:fs';
import http from 'node:http';
import https from 'node:https';
import net from 'node:net';
import tls from 'node:tls';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const SEEDS_FILE = process.env.SEEDS_FILE || path.join(ROOT, 'seeds.json');
const OUT_FILE = process.env.OUT_FILE || path.join(ROOT, 'streams.json');

const RB_BASES = process.env.RB_BASE
  ? [process.env.RB_BASE]
  : ['https://de1.api.radio-browser.info', 'https://de2.api.radio-browser.info', 'https://nl1.api.radio-browser.info', 'https://at1.api.radio-browser.info'];

const PROBE_TIMEOUT_MS = Number(process.env.PROBE_TIMEOUT_MS || 10000);
const PROBE_MIN_BYTES = 8192;          // koľko zvukových dát musí dôjsť, aby sa stream považoval za živý
const CONCURRENCY = 8;
const PROMOTE_AFTER = 5;               // koľko rôznych dní musí nový stream prejsť, kým ide do hlavnej ponuky
const DROP_AFTER_FAILS = 4;            // objavená (nie kurátorovaná) adresa sa zahodí po toľkých zlyhaniach za sebou
const MAX_NEW = 30;                    // najviac nových staníc v skupine „new“
const MIN_KBPS_NEW = 64;               // nové stanice pod týmto bitrate sa nezaraďujú
const TODAY = new Date().toISOString().slice(0, 10);

const log = (...a) => console.log(...a);
const sleep = ms => new Promise(r => setTimeout(r, ms));
const norm = s => (s || '').normalize('NFD').replace(/[\u0300-\u036f]/g, '').toLowerCase()
  .replace(/[^a-z0-9]+/g, ' ').replace(/\b(radio|online|live|stream)\b/g, ' ').replace(/\s+/g, ' ').trim();
const normLoose = s => (s || '').normalize('NFD').replace(/[̀-ͯ]/g, '').toLowerCase().replace(/[_\-]+/g, ' ');
const isHttps = u => /^https:/i.test(u);

function typeFromCodec(codec, ct) {
  const c = `${codec || ''} ${ct || ''}`.toLowerCase();
  if (/aac/.test(c)) return 'audio/aac';
  if (/ogg|vorbis|opus/.test(c)) return 'audio/ogg';
  return 'audio/mpeg';
}

// ---------------------------------------------------------------- overenie jednej adresy
// Záloha pre staré Shoutcast servery: odpovedajú "ICY 200 OK", čo HTTP parser v Node odmieta, preto si odpoveď prečítame sami.
function rawProbe(u) {
  return new Promise(resolve => {
    const secure = u.protocol === 'https:';
    const port = Number(u.port) || (secure ? 443 : 80);
    let buf = Buffer.alloc(0), headEnd = -1, head = null, settled = false, bodyBytes = 0;
    const done = r => { if (!settled) { settled = true; clearTimeout(timer); try { sock.destroy(); } catch { /* nič */ } resolve(r); } };
    const timer = setTimeout(() => done({ ok: false, reason: 'timeout' }), PROBE_TIMEOUT_MS);
    const onConnect = () => sock.write(`GET ${u.pathname}${u.search} HTTP/1.0\r\nHost: ${u.host}\r\nUser-Agent: igor-stream-checker/1.0\r\nIcy-MetaData: 0\r\nAccept: */*\r\nConnection: close\r\n\r\n`);
    const sock = secure ? tls.connect({ host: u.hostname, port, servername: u.hostname }, onConnect) : net.connect({ host: u.hostname, port }, onConnect);
    sock.on('error', e => done({ ok: false, reason: 'net:' + (e.code || e.message) }));
    sock.on('end', () => done({ ok: false, reason: 'ended' }));
    sock.on('data', d => {
      if (headEnd < 0) {
        buf = Buffer.concat([buf, d]);
        const i = buf.indexOf('\r\n\r\n');
        if (i < 0) { if (buf.length > 16384) done({ ok: false, reason: 'bad-header' }); return; }
        headEnd = i + 4;
        const lines = buf.slice(0, i).toString('latin1').split('\r\n');
        const m = /^(?:ICY|HTTP\/\d\.\d)\s+(\d{3})/i.exec(lines[0]);
        if (!m || m[1] !== '200') return done({ ok: false, reason: 'http-' + (m ? m[1] : 'bad') });
        head = {};
        for (const l of lines.slice(1)) { const k = l.indexOf(':'); if (k > 0) head[l.slice(0, k).trim().toLowerCase()] = l.slice(k + 1).trim(); }
        const ct = (head['content-type'] || '').toLowerCase();
        if (/text\/html|application\/json/.test(ct)) return done({ ok: false, reason: 'not-audio:' + ct });
        bodyBytes = buf.length - headEnd;
      } else bodyBytes += d.length;
      if (head && bodyBytes >= PROBE_MIN_BYTES) {
        const br = parseInt(head['icy-br'], 10);
        done({ ok: true, ct: (head['content-type'] || '').toLowerCase(), icyBr: Number.isFinite(br) ? br : null, bytes: bodyBytes });
      }
    });
  });
}


// Používa http/https moduly s insecureHTTPParser, lebo bežný fetch odmietne staré Shoutcast odpovede ("ICY 200 OK").
function probe(url, redirects = 3) {
  return new Promise(resolve => {
    let u;
    try { u = new URL(url); } catch { return resolve({ ok: false, reason: 'bad-url' }); }
    const mod = u.protocol === 'https:' ? https : u.protocol === 'http:' ? http : null;
    if (!mod) return resolve({ ok: false, reason: 'bad-protocol' });
    let settled = false;
    const done = r => { if (!settled) { settled = true; clearTimeout(timer); try { req.destroy(); } catch { /* nič */ } resolve(r); } };
    const timer = setTimeout(() => done({ ok: false, reason: 'timeout' }), PROBE_TIMEOUT_MS);
    const req = mod.get(u, { headers: { 'User-Agent': 'igor-stream-checker/1.0', 'Icy-MetaData': '0', Accept: '*/*' }, insecureHTTPParser: true }, res => {
      const code = res.statusCode || 0;
      if (code >= 300 && code < 400 && res.headers.location) {
        res.resume();
        if (redirects <= 0) return done({ ok: false, reason: 'redirects' });
        clearTimeout(timer);
        settled = true;
        return resolve(probe(new URL(res.headers.location, u).toString(), redirects - 1));
      }
      if (code !== 200) { res.resume(); return done({ ok: false, reason: 'http-' + code }); }
      const ct = String(res.headers['content-type'] || '').toLowerCase();
      if (/text\/html|application\/json|text\/plain.*charset/.test(ct) && !/audio|ogg|mpeg/.test(ct)) { res.resume(); return done({ ok: false, reason: 'not-audio:' + ct }); }
      if (/mpegurl|x-scpls|text\/plain/.test(ct)) { res.resume(); return done({ ok: false, reason: 'playlist:' + ct }); }
      const icyBr = parseInt(res.headers['icy-br'], 10);
      let got = 0;
      res.on('data', d => { got += d.length; if (got >= PROBE_MIN_BYTES) done({ ok: true, ct, icyBr: Number.isFinite(icyBr) ? icyBr : null, bytes: got }); });
      res.on('end', () => done({ ok: got >= PROBE_MIN_BYTES, reason: 'ended', ct }));
      res.on('error', () => done({ ok: false, reason: 'stream-error' }));
    });
    req.on('error', e => {
      if (settled) return;
      if (/^HPE_/.test(e.code || '')) {                       // „ICY 200 OK“ a podobné – skúsime surový socket
        clearTimeout(timer); settled = true;
        return resolve(rawProbe(u));
      }
      done({ ok: false, reason: 'net:' + (e.code || e.message) });
    });
  });
}

async function pool(items, worker, n = CONCURRENCY) {
  const q = [...items]; const out = [];
  await Promise.all(Array.from({ length: n }, async () => { while (q.length) { const it = q.shift(); out.push(await worker(it)); } }));
  return out;
}

// ---------------------------------------------------------------- radio-browser.info
async function rb(pathAndQuery) {
  for (const base of RB_BASES) {
    for (let attempt = 0; attempt < 2; attempt++) {
      try {
        const r = await fetch(base + pathAndQuery, { headers: { 'User-Agent': 'igor-stream-checker/1.0' }, signal: AbortSignal.timeout(20000) });
        if (r.ok) { const j = await r.json(); if (Array.isArray(j)) return j; }
      } catch { /* skúsime znova / iný server */ }
      await sleep(500);
    }
  }
  return null;
}
const rbQuery = o => '/json/stations/search?' + new URLSearchParams({ hidebroken: 'true', order: 'clickcount', reverse: 'true', ...o });

function rbToCand(x) {
  const url = x.url_resolved || x.url;
  if (!url || !/^https?:/i.test(url) || x.hls === 1) return null;
  return { url, kbps: x.bitrate > 0 ? x.bitrate : null, type: typeFromCodec(x.codec), clicks: x.clickcount || 0, name: x.name };
}

// ---------------------------------------------------------------- hlavná logika
async function main() {
  const seeds = JSON.parse(fs.readFileSync(SEEDS_FILE, 'utf8'));
  let prev = { stations: [] };
  try { prev = JSON.parse(fs.readFileSync(OUT_FILE, 'utf8')); } catch { /* prvý beh */ }
  const prevById = new Map((prev.stations || []).map(s => [s.id, s]));
  const prevUrlFails = new Map();
  for (const s of prev.stations || []) for (const u of s.urls || []) prevUrlFails.set(u.url, { fails: u.fails || 0, date: u.failDate || null });

  // --- 1) objavovanie
  log('Sťahujem zoznam slovenských staníc z radio-browser.info…');
  const skList = await rb(rbQuery({ countrycode: 'SK', limit: '400' }));
  if (!skList) { log('radio-browser.info neodpovedá – ponechávam existujúci streams.json.'); return; }
  const skCands = skList.map(rbToCand).filter(Boolean);
  log(`  ${skCands.length} slovenských záznamov`);

  const seedExtra = new Map();     // id -> kandidáti nájdení hľadaním podľa názvu (CZ/hudobné/SK)
  for (const s of seeds.stations) {
    if (!s.search) continue;
    const q = { name: s.search, limit: '25' };
    if (s.country) q.countrycode = s.country;
    const list = await rb(rbQuery(q));
    if (!list) continue;
    const m = normLoose(s.match || s.search);
    seedExtra.set(s.id, list.map(rbToCand).filter(c => c && normLoose(c.name).includes(m)).slice(0, 8));
  }

  // --- 2) zostavenie kandidátov pre kurátorované stanice
  const seedIdByName = new Map();
  const stations = seeds.stations.map(s => {
    const cands = new Map();
    const add = (c, fromSeed) => { if (c && !cands.has(c.url)) cands.set(c.url, { url: c.url, kbps: c.kbps || null, type: c.type || typeFromCodec('', ''), seed: !!fromSeed }); };
    s.urls.forEach(c => add(c, true));
    (seedExtra.get(s.id) || []).forEach(c => add(c, false));
    // SK stanice z veľkého zoznamu, ktoré patria k tejto stanici
    if (s.country === 'SK' && s.match) {
      const m = normLoose(s.match);
      skCands.filter(c => normLoose(c.name).includes(m) && norm(c.name) === norm(s.name)).slice(0, 6).forEach(c => add(c, false));
    }
    seedIdByName.set(norm(s.name), s.id);
    return { id: s.id, group: s.group, name: s.name, curated: true, cands };
  });

  // --- 3) nové stanice (nie sú v seeds): zoskupené podľa normalizovaného názvu
  const known = new Set(stations.map(s => norm(s.name)));
  const newByName = new Map();
  for (const c of skCands) {
    const key = norm(c.name);
    if (!key || key.length < 3 || known.has(key)) continue;
    if (c.kbps && c.kbps < MIN_KBPS_NEW) continue;
    if (!newByName.has(key)) newByName.set(key, { name: c.name.trim(), cands: new Map(), clicks: 0 });
    const g = newByName.get(key);
    g.clicks += c.clicks;
    if (!g.cands.has(c.url)) g.cands.set(c.url, { url: c.url, kbps: c.kbps, type: c.type, seed: false });
  }
  const topNew = [...newByName.entries()].sort((a, b) => b[1].clicks - a[1].clicks).slice(0, MAX_NEW * 2);
  const newStations = topNew.map(([key, g]) => ({
    id: 'n-' + key.replace(/\s+/g, '-'), group: 'new', name: g.name, curated: false, cands: g.cands, clicks: g.clicks
  }));

  // sem pridáme aj stanice, ktoré sme už v minulosti našli (aby sme ich nestratili, ak v API na chvíľu chýbajú)
  for (const p of prev.stations || []) {
    if (p.curated || stations.some(s => s.id === p.id) || newStations.some(s => s.id === p.id)) continue;
    const cands = new Map((p.urls || []).map(u => [u.url, { url: u.url, kbps: u.kbps, type: u.type, seed: false }]));
    newStations.push({ id: p.id, group: p.group, name: p.name, curated: false, cands, clicks: 0 });
  }

  // --- 4) overenie všetkých adries
  const all = [...stations, ...newStations];
  const jobs = [];
  for (const st of all) for (const c of st.cands.values()) jobs.push({ st, c });
  log(`Overujem ${jobs.length} adries (${all.length} staníc)…`);
  await pool(jobs, async ({ c }) => {
    const r = await probe(c.url);
    c.ok = r.ok; c.reason = r.reason;
    if (r.ok) {
      if (r.icyBr && !c.kbps) c.kbps = r.icyBr;
      if (/aac/.test(r.ct || '')) c.type = 'audio/aac'; else if (/ogg/.test(r.ct || '')) c.type = 'audio/ogg'; else if (/mpeg|mp3/.test(r.ct || '')) c.type = 'audio/mpeg';
    }
  });

  // poistka: ak takmer nič neprešlo, problém je pravdepodobne v sieti runnera, nie v streamoch
  const okCount = jobs.filter(j => j.c.ok).length;
  log(`  ${okCount}/${jobs.length} adries funguje`);
  if (jobs.length > 10 && okCount / jobs.length < 0.1) { log('Príliš málo funkčných adries – vyzerá to na výpadok siete. Ponechávam existujúci streams.json.'); return; }

  // --- 5) zostavenie výstupu
  const rank = (a, b) => (b.kbps || 0) - (a.kbps || 0) || (isHttps(b.url) - isHttps(a.url));
  const out = [];
  for (const st of all) {
    const old = prevById.get(st.id);
    const urls = [];
    for (const c of st.cands.values()) {
      const pf = prevUrlFails.get(c.url) || { fails: 0, date: null };
      const failDate = c.ok ? null : TODAY;
      const fails = c.ok ? 0 : (pf.date === TODAY ? pf.fails : pf.fails + 1);     // počíta sa najviac jedno zlyhanie za deň
      if (!c.ok && !c.seed && fails >= DROP_AFTER_FAILS) continue;          // dlhodobo mŕtva objavená adresa
      const entry = { url: c.url, kbps: c.kbps || null, type: c.type, https: isHttps(c.url), verified: !!c.ok, fails };
      if (failDate) entry.failDate = failDate;
      urls.push(entry);
    }
    urls.sort((a, b) => (b.verified - a.verified) || rank(a, b));
    const anyOk = urls.some(u => u.verified);

    let group = st.group, okDays = old ? old.okDays || 0 : 0, firstSeen = old ? old.firstSeen : TODAY, lastOkDate = old ? old.lastOkDate : null;
    if (anyOk && lastOkDate !== TODAY) { okDays++; lastOkDate = TODAY; }
    if (!anyOk && !st.curated && !old) continue;                            // nová a hneď nefunkčná – nezaradíme
    if (!st.curated) {
      const promoted = old ? (old.group !== 'new') : false;
      if (promoted || okDays >= PROMOTE_AFTER) group = 'sk';
      else group = 'new';
      if (!anyOk && okDays === 0) continue;
    }
    out.push({ id: st.id, group, name: st.name, curated: st.curated, firstSeen, lastOkDate, okDays, urls: urls.slice(0, 6) });
  }

  // nové stanice: najviac MAX_NEW v skupine „new“ (podľa obľúbenosti), povýšené ostávajú
  const newOnes = out.filter(s => s.group === 'new');
  if (newOnes.length > MAX_NEW) {
    const clicks = new Map(newStations.map(s => [s.id, s.clicks || 0]));
    newOnes.sort((a, b) => (clicks.get(b.id) || 0) - (clicks.get(a.id) || 0));
    const drop = new Set(newOnes.slice(MAX_NEW).map(s => s.id));
    for (let i = out.length - 1; i >= 0; i--) if (drop.has(out[i].id)) out.splice(i, 1);
  }

  const result = { generated: TODAY, groups: { ...seeds.groups, new: 'Nové nájdené (overuje sa)' }, stations: out };
  const strip = o => JSON.stringify({ groups: o.groups, stations: o.stations });
  if (prev.stations && strip(prev) === strip(result)) { log('Žiadna zmena – streams.json sa nepíše.'); return; }
  fs.writeFileSync(OUT_FILE, JSON.stringify(result, null, 1) + '\n');
  const nNew = out.filter(s => s.group === 'new').length;
  log(`Zapísané: ${out.length} staníc (z toho ${nNew} nových v overovaní).`);
}

main().catch(e => { console.error('Chyba:', e); process.exit(1); });
