/* Kichik QR kod yaratuvchi: bayt rejimi, xatolarni tuzatish darajasi L, 1–5 versiyalar (106 baytgacha).
   Tashqi kutubxonasiz. Ish tartibi: ma'lumot → Rid-Solomon → modullarni joylash → niqob tanlash → format ma'lumoti. */

const EC = { 1: [19, 7], 2: [34, 10], 3: [55, 15], 4: [80, 20], 5: [108, 26] };
const AP = { 1: [], 2: [6, 18], 3: [6, 22], 4: [6, 26], 5: [6, 30] };

const EXP = new Array(512), LOG = new Array(256);
(function () {
  let x = 1;
  for (let i = 0; i < 255; i++) { EXP[i] = x; LOG[x] = i; x <<= 1; if (x & 256) x ^= 0x11d; }
  for (let i = 255; i < 512; i++) EXP[i] = EXP[i - 255];
})();
const gmul = (a, b) => (a === 0 || b === 0 ? 0 : EXP[LOG[a] + LOG[b]]);

function rsRemainder(data, n) {
  let g = [1];
  for (let i = 0; i < n; i++) {
    const ng = new Array(g.length + 1).fill(0);
    for (let j = 0; j < g.length; j++) { ng[j] ^= g[j]; ng[j + 1] ^= gmul(g[j], EXP[i]); }
    g = ng;
  }
  const rem = new Array(n).fill(0);
  for (const b of data) {
    const f = b ^ rem.shift(); rem.push(0);
    for (let i = 0; i < n; i++) rem[i] ^= gmul(g[i + 1], f);
  }
  return rem;
}

const MASKS = [
  (r, c) => (r + c) % 2 === 0,
  (r) => r % 2 === 0,
  (r, c) => c % 3 === 0,
  (r, c) => (r + c) % 3 === 0,
  (r, c) => (Math.floor(r / 2) + Math.floor(c / 3)) % 2 === 0,
  (r, c) => ((r * c) % 2) + ((r * c) % 3) === 0,
  (r, c) => (((r * c) % 2) + ((r * c) % 3)) % 2 === 0,
  (r, c) => ((((r + c) % 2) + ((r * c) % 3)) % 2) === 0
];

function penalty(m, n) {
  let p = 0, dark = 0;
  for (let r = 0; r < n; r++) for (let c = 0; c < n; c++) if (m[r][c]) dark++;
  const line = (get) => {
    let run = 1, pt = 0;
    for (let i = 1; i < n; i++) {
      if (get(i) === get(i - 1)) { run++; } else { if (run >= 5) pt += 3 + (run - 5); run = 1; }
    }
    if (run >= 5) pt += 3 + (run - 5);
    return pt;
  };
  for (let i = 0; i < n; i++) { p += line((k) => m[i][k]); p += line((k) => m[k][i]); }
  for (let r = 0; r < n - 1; r++) for (let c = 0; c < n - 1; c++) { const v = m[r][c]; if (v === m[r][c + 1] && v === m[r + 1][c] && v === m[r + 1][c + 1]) p += 3; }
  const pat = [1, 0, 1, 1, 1, 0, 1];
  const chk = (get, i) => {
    for (let s = 0; s + 11 <= n; s++) {
      let a = true, b = true;
      for (let k = 0; k < 7; k++) { if (get(i, s + k) !== !!pat[k]) a = false; if (get(i, s + 4 + k) !== !!pat[k]) b = false; }
      if (a) { let z = true; for (let k = 7; k < 11; k++) if (get(i, s + k)) z = false; if (z) p += 40; }
      if (b) { let z = true; for (let k = 0; k < 4; k++) if (get(i, s + k)) z = false; if (z) p += 40; }
    }
  };
  for (let i = 0; i < n; i++) { chk((a, b) => m[a][b], i); chk((a, b) => m[b][a], i); }
  p += Math.floor(Math.abs((dark * 100) / (n * n) - 50) / 5) * 10;
  return p;
}

export function qrMatrix(text) {
  const bytes = Array.from(new TextEncoder().encode(text));
  let ver = 0;
  for (let i = 1; i <= 5; i++) if (bytes.length <= EC[i][0] - 2) { ver = i; break; }
  if (!ver) throw new Error('QR: matn juda uzun');
  const [dataCw, ecCw] = EC[ver];
  const bits = [];
  const put = (v, len) => { for (let i = len - 1; i >= 0; i--) bits.push((v >>> i) & 1); };
  put(4, 4); put(bytes.length, 8);
  bytes.forEach((b) => put(b, 8));
  const cap = dataCw * 8;
  for (let i = 0; i < 4 && bits.length < cap; i++) bits.push(0);
  while (bits.length % 8) bits.push(0);
  for (let pad = 0xec; bits.length < cap; pad ^= 0xec ^ 0x11) put(pad, 8);
  const data = [];
  for (let i = 0; i < bits.length; i += 8) { let b = 0; for (let k = 0; k < 8; k++) b = (b << 1) | bits[i + k]; data.push(b); }
  const all = data.concat(rsRemainder(data, ecCw));
  const stream = [];
  all.forEach((b) => { for (let i = 7; i >= 0; i--) stream.push((b >>> i) & 1); });

  const n = 17 + 4 * ver;
  const mk = () => Array.from({ length: n }, () => new Array(n).fill(false));
  const mod = mk(), fn = mk();
  const setF = (r, c, v) => { if (r < 0 || c < 0 || r >= n || c >= n) return; mod[r][c] = !!v; fn[r][c] = true; };
  // izlovchi naqshlar
  [[0, 0], [0, n - 7], [n - 7, 0]].forEach(([r0, c0]) => {
    for (let dr = -1; dr <= 7; dr++) for (let dc = -1; dc <= 7; dc++) {
      const d = Math.max(Math.abs(dr - 3), Math.abs(dc - 3));
      setF(r0 + dr, c0 + dc, d !== 2 && d !== 4);
    }
  });
  // vaqt chiziqlari
  for (let i = 8; i < n - 8; i++) { setF(6, i, i % 2 === 0); setF(i, 6, i % 2 === 0); }
  // tekislash naqshlari
  const ap = AP[ver];
  ap.forEach((r) => ap.forEach((c) => {
    if ((r === 6 && c === 6) || (r === 6 && c === ap[ap.length - 1]) || (r === ap[ap.length - 1] && c === 6)) return;
    for (let dr = -2; dr <= 2; dr++) for (let dc = -2; dc <= 2; dc++) setF(r + dr, c + dc, Math.max(Math.abs(dr), Math.abs(dc)) !== 1);
  }));
  // format maydonlarini band qilish
  for (let i = 0; i < 9; i++) { if (i !== 6) { setF(8, i, false); setF(i, 8, false); } }
  for (let i = 0; i < 8; i++) { setF(8, n - 1 - i, false); setF(n - 1 - i, 8, false); }
  setF(n - 8, 8, true);

  // ma'lumotni zigzag joylash
  const place = [];
  let idx = 0, up = true;
  for (let right = n - 1; right >= 1; right -= 2) {
    if (right === 6) right = 5;
    for (let k = 0; k < n; k++) {
      const r = up ? n - 1 - k : k;
      for (let j = 0; j < 2; j++) {
        const c = right - j;
        if (!fn[r][c]) { place.push([r, c, idx < stream.length ? stream[idx] : 0]); idx++; }
      }
    }
    up = !up;
  }

  const fmt = (mask) => {
    const d = (1 << 3) | mask; // L = 01
    let rem = d;
    for (let i = 0; i < 10; i++) rem = (rem << 1) ^ ((rem >>> 9) * 0x537);
    return ((d << 10) | rem) ^ 0x5412;
  };
  const bit = (x, i) => ((x >>> i) & 1) === 1;
  const build = (mask) => {
    const m = mod.map((row) => row.slice());
    place.forEach(([r, c, b]) => { m[r][c] = (b === 1) !== MASKS[mask](r, c); });
    const f = fmt(mask);
    for (let i = 0; i <= 5; i++) m[i][8] = bit(f, i);
    m[7][8] = bit(f, 6); m[8][8] = bit(f, 7); m[8][7] = bit(f, 8);
    for (let i = 9; i < 15; i++) m[8][14 - i] = bit(f, i);
    for (let i = 0; i < 8; i++) m[8][n - 1 - i] = bit(f, i);
    for (let i = 8; i < 15; i++) m[n - 15 + i][8] = bit(f, i);
    m[n - 8][8] = true;
    return m;
  };
  let best = null, bestP = Infinity;
  for (let k = 0; k < 8; k++) { const m = build(k), p = penalty(m, n); if (p < bestP) { bestP = p; best = m; } }
  return best;
}

/* Kanvasga oq fon, qora modullar va 4 modullik bo'sh chekka bilan chizish. */
export function drawQr(canvas, text, px) {
  const m = qrMatrix(text), n = m.length, q = 4;
  const sc = Math.max(2, Math.floor(px / (n + q * 2)));
  const size = sc * (n + q * 2);
  canvas.width = size; canvas.height = size;
  const g = canvas.getContext('2d');
  g.fillStyle = '#fff'; g.fillRect(0, 0, size, size);
  g.fillStyle = '#000';
  for (let r = 0; r < n; r++) for (let c = 0; c < n; c++) if (m[r][c]) g.fillRect((c + q) * sc, (r + q) * sc, sc, sc);
}
