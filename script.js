
let logs = [];
let simpleLogs = [];
let mode = 'encrypt';
let W = 32;

function log(msg, type = '') {
  logs.push({ msg, type });
}


function simpleLog(title, text) {
  simpleLogs.push({ title, text });
}

/* =========================================================
   Bagian ini menyiapkan aturan dasar RC5 sesuai pilihan user.
   Contohnya word size, konstanta P/Q, dan ukuran blok.
   ========================================================= */
function getConfig(w) {
  const bits = BigInt(w);
  const mod = 1n << bits;
  const mask = mod - 1n;

  let P, Q;
  if (w === 16) {
    P = 0xB7E1n;
    Q = 0x9E37n;
  } else if (w === 32) {
    P = 0xB7E15163n;
    Q = 0x9E3779B9n;
  } else if (w === 64) {
    P = 0xB7E151628AED2A6Bn;
    Q = 0x9E3779B97F4A7C15n;
  } else {
    throw new Error('Word size hanya boleh 16, 32, atau 64 bit.');
  }

  return {
    w,
    bits,
    mod,
    mask,
    P,
    Q,
    u: w / 8,          // jumlah byte per word
    blockSize: w / 4   // 2 word per blok = 2 * (w/8) = w/4 byte
  };
}

function modAdd(a, b, cfg) {
  return (a + b) & cfg.mask;
}

function modSub(a, b, cfg) {
  return (a - b) & cfg.mask;
}

function rotL(x, y, cfg) {
  x = x & cfg.mask;
  const s = Number(y % cfg.bits);
  if (s === 0) return x;
  return ((x << BigInt(s)) | (x >> BigInt(cfg.w - s))) & cfg.mask;
}

function rotR(x, y, cfg) {
  x = x & cfg.mask;
  const s = Number(y % cfg.bits);
  if (s === 0) return x;
  return ((x >> BigInt(s)) | (x << BigInt(cfg.w - s))) & cfg.mask;
}

function xor(a, b, cfg) {
  return (a ^ b) & cfg.mask;
}

function hexWord(x, cfg) {
  return '0x' + (x & cfg.mask).toString(16).toUpperCase().padStart(cfg.u * 2, '0');
}

function hexByte(x) {
  return x.toString(16).toUpperCase().padStart(2, '0');
}

function shiftInfo(value, cfg) {
  return Number(value % cfg.bits);
}

function bytesText(bytes) {
  return bytes.map(hexByte).join(' ');
}

/* =========================================================
   Bagian bantu untuk ubah teks menjadi byte, byte menjadi teks,
   dan mengatur padding supaya panjang data pas dengan ukuran blok.
   ========================================================= */
function keyToBytes(key, keyLength) {
  const bytes = [];
  for (let i = 0; i < keyLength; i++) {
    bytes.push(i < key.length ? key.charCodeAt(i) & 0xFF : 0);
  }
  return bytes;
}

function textToBytes(text) {
  const bytes = [];
  for (let i = 0; i < text.length; i++) {
    const code = text.charCodeAt(i);
    if (code <= 0x7F) {
      bytes.push(code);
    } else if (code <= 0x7FF) {
      bytes.push(0xC0 | (code >> 6));
      bytes.push(0x80 | (code & 0x3F));
    } else {
      bytes.push(0xE0 | (code >> 12));
      bytes.push(0x80 | ((code >> 6) & 0x3F));
      bytes.push(0x80 | (code & 0x3F));
    }
  }
  return bytes;
}

function bytesToText(bytes) {
  let result = '';
  for (let i = 0; i < bytes.length; i++) {
    const b1 = bytes[i];
    if (b1 < 0x80) {
      result += String.fromCharCode(b1);
    } else if ((b1 & 0xE0) === 0xC0) {
      const b2 = bytes[++i];
      result += String.fromCharCode(((b1 & 0x1F) << 6) | (b2 & 0x3F));
    } else if ((b1 & 0xF0) === 0xE0) {
      const b2 = bytes[++i];
      const b3 = bytes[++i];
      result += String.fromCharCode(((b1 & 0x0F) << 12) | ((b2 & 0x3F) << 6) | (b3 & 0x3F));
    }
  }
  return result;
}

function bytesToWord(bytes, start, cfg) {
  let word = 0n;
  for (let i = 0; i < cfg.u; i++) {
    word |= BigInt(bytes[start + i]) << BigInt(8 * i);
  }
  return word & cfg.mask;
}

function wordToBytes(word, cfg) {
  const bytes = [];
  word = word & cfg.mask;
  for (let i = 0; i < cfg.u; i++) {
    bytes.push(Number((word >> BigInt(8 * i)) & 0xFFn));
  }
  return bytes;
}

function padBytes(bytes, blockSize) {
  const pad = blockSize - (bytes.length % blockSize);
  const result = bytes.slice();
  for (let i = 0; i < pad; i++) result.push(pad);
  return result;
}

function unpadBytes(bytes, blockSize) {
  if (bytes.length === 0) return bytes;
  const pad = bytes[bytes.length - 1];
  if (pad < 1 || pad > blockSize || pad > bytes.length) {
    throw new Error('Padding tidak valid. Kunci, parameter, atau ciphertext salah.');
  }
  for (let i = bytes.length - pad; i < bytes.length; i++) {
    if (bytes[i] !== pad) {
      throw new Error('Padding tidak valid. Kunci, parameter, atau ciphertext salah.');
    }
  }
  return bytes.slice(0, bytes.length - pad);
}

function hexToBytes(hex) {
  const bytes = [];
  for (let i = 0; i < hex.length; i += 2) {
    bytes.push(parseInt(hex.substring(i, i + 2), 16));
  }
  return bytes;
}

function bytesToHex(bytes) {
  return bytes.map(hexByte).join('');
}

/* =========================================================
   Key expansion: kunci asli dipanjangkan menjadi banyak sub-key.
   Sub-key inilah yang dipakai berulang-ulang saat enkripsi/dekripsi.
   ========================================================= */
function keyExpansion(key, rounds, keyLength, wordSize) {
  const cfg = getConfig(wordSize);
  const c = Math.max(1, Math.ceil(keyLength / cfg.u));
  const t = 2 * (rounds + 1);
  const keyBytes = keyToBytes(key, keyLength);
  const L = new Array(c).fill(0n);
  const S = new Array(t).fill(0n);

  log('=== KEY EXPANSION ===', 'step');
  log(`w=${wordSize}, r=${rounds}, b=${keyLength}, u=${cfg.u}, c=${c}, t=${t}`);

  for (let i = keyLength - 1; i >= 0; i--) {
    const index = Math.floor(i / cfg.u);
    L[index] = ((L[index] << 8n) + BigInt(keyBytes[i])) & cfg.mask;
  }

  log(`L: [${L.map(v => hexWord(v, cfg)).join(', ')}]`, 'val');

  S[0] = cfg.P;
  for (let i = 1; i < t; i++) {
    S[i] = modAdd(S[i - 1], cfg.Q, cfg);
  }

  log(`P = ${hexWord(cfg.P, cfg)}, Q = ${hexWord(cfg.Q, cfg)}`, 'val');
  log(`S[0] = ${hexWord(S[0], cfg)}`, 'val');

  let A = 0n;
  let B = 0n;
  let i = 0;
  let j = 0;
  const n = 3 * Math.max(t, c);

  for (let k = 0; k < n; k++) {
    A = S[i] = rotL(modAdd(modAdd(S[i], A, cfg), B, cfg), 3n, cfg);
    B = L[j] = rotL(modAdd(modAdd(L[j], A, cfg), B, cfg), modAdd(A, B, cfg), cfg);
    i = (i + 1) % t;
    j = (j + 1) % c;
  }

  log(`Mixing selesai — ${n} iterasi. Sub-key S[0..${t - 1}] siap.`);
  return { S, cfg };
}

/* =========================================================
   Ini bagian utama  RC5 untuk 1 blok data.
   Data dibagi menjadi A dan B, lalu diputar, di-XOR, dan ditambah sub-key.
   ========================================================= */
function encBlockDetailed(A, B, S, rounds, cfg) {
  const steps = [];
  const awalA = A;
  const awalB = B;

  const afterAddA = modAdd(A, S[0], cfg);
  const afterAddB = modAdd(B, S[1], cfg);

  steps.push(`Data blok dibaca menjadi dua bagian: A=${hexWord(awalA, cfg)} dan B=${hexWord(awalB, cfg)}.`);
  steps.push(`Langkah awal A: (${hexWord(awalA, cfg)} + S[0] ${hexWord(S[0], cfg)}) mod 2^${cfg.w} = ${hexWord(afterAddA, cfg)}.`);
  steps.push(`Langkah awal B: (${hexWord(awalB, cfg)} + S[1] ${hexWord(S[1], cfg)}) mod 2^${cfg.w} = ${hexWord(afterAddB, cfg)}.`);

  A = afterAddA;
  B = afterAddB;

  for (let i = 1; i <= rounds; i++) {
    const oldA = A;
    const oldB = B;

    const xorA = xor(oldA, oldB, cfg);
    const geserA = shiftInfo(oldB, cfg);
    const rotA = rotL(xorA, oldB, cfg);
    const newA = modAdd(rotA, S[2 * i], cfg);

    const xorB = xor(oldB, newA, cfg);
    const geserB = shiftInfo(newA, cfg);
    const rotB = rotL(xorB, newA, cfg);
    const newB = modAdd(rotB, S[2 * i + 1], cfg);

    steps.push(
      `Putaran ${i}:
` +
      `A = ROTL(A XOR B, B) + S[${2 * i}]
` +
      `  = ROTL(${hexWord(oldA, cfg)} XOR ${hexWord(oldB, cfg)} = ${hexWord(xorA, cfg)}, geser ${geserA}) + ${hexWord(S[2 * i], cfg)}
` +
      `  = ${hexWord(rotA, cfg)} + ${hexWord(S[2 * i], cfg)} = ${hexWord(newA, cfg)}
` +
      `B = ROTL(B XOR A, A) + S[${2 * i + 1}]
` +
      `  = ROTL(${hexWord(oldB, cfg)} XOR ${hexWord(newA, cfg)} = ${hexWord(xorB, cfg)}, geser ${geserB}) + ${hexWord(S[2 * i + 1], cfg)}
` +
      `  = ${hexWord(rotB, cfg)} + ${hexWord(S[2 * i + 1], cfg)} = ${hexWord(newB, cfg)}`
    );

    A = newA;
    B = newB;
  }

  return { A, B, steps };
}

function encBlock(A, B, S, rounds, cfg) {
  const hasil = encBlockDetailed(A, B, S, rounds, cfg);
  return [hasil.A, hasil.B];
}

function decBlock(A, B, S, rounds, cfg) {
  for (let i = rounds; i >= 1; i--) {
    B = xor(rotR(modSub(B, S[2 * i + 1], cfg), A, cfg), A, cfg);
    A = xor(rotR(modSub(A, S[2 * i], cfg), B, cfg), B, cfg);
  }

  B = modSub(B, S[1], cfg);
  A = modSub(A, S[0], cfg);

  return [A, B];
}

/* =========================================================
   Bagian ini mengurus data utuh dari input user.
   Kalau datanya panjang, data akan dipotong menjadi beberapa blok.
   ========================================================= */
function encryptRC5(plaintext, key, rounds, keyLength, wordSize) {
  logs = [];
  simpleLogs = [];
  log('=== ENKRIPSI RC5 ===', 'step');
  log(`Plaintext: "${plaintext}"`, 'val');
  simpleLog('1. Data diterima', `Teks yang mau diamankan adalah "${plaintext}". Kunci yang dipakai tidak ditampilkan di hasil, tapi dipakai untuk mengacak isi pesan.`);

  const expanded = keyExpansion(key, rounds, keyLength, wordSize);
  const S = expanded.S;
  const cfg = expanded.cfg;
  simpleLog('2. Kunci diproses', `Kunci diolah dulu menjadi banyak sub-key. Tujuannya supaya proses acaknya tidak hanya bergantung pada teks kunci mentah.`);
  simpleLog('3. Aturan RC5 dipakai', `Mode yang berjalan adalah RC5-${wordSize}/${rounds}/${keyLength}. Artinya ukuran kata ${wordSize} bit, putaran ${rounds} kali, dan panjang kunci ${keyLength} byte.`);

  let bytes = textToBytes(plaintext);

  log('\n=== PROSES BLOK ===', 'step');
  log(`Byte awal: [${bytes.map(hexByte).join(' ')}]`, 'val');

  const originalBytes = bytes.slice();
  bytes = padBytes(bytes, cfg.blockSize);
  log(`Setelah padding: ${bytes.length} byte — ${bytes.length / cfg.blockSize} blok`);
  simpleLog('4. Teks diubah menjadi byte', `Komputer membaca teks sebagai angka byte. Untuk input ini, byte awalnya adalah [${bytesText(originalBytes)}]. Karena ukuran blok RC5-${wordSize} adalah ${cfg.blockSize} byte, data ditambah padding menjadi [${bytesText(bytes)}].`);
  simpleLog('5. Data dibagi per blok', `Total data setelah padding adalah ${bytes.length} byte, sehingga menjadi ${bytes.length / cfg.blockSize} blok. Setiap blok berisi dua bagian, yaitu A dan B.`);

  const cipherBytes = [];

  for (let pos = 0; pos < bytes.length; pos += cfg.blockSize) {
    let A = bytesToWord(bytes, pos, cfg);
    let B = bytesToWord(bytes, pos + cfg.u, cfg);

    log(`Blok ${pos / cfg.blockSize + 1}: A=${hexWord(A, cfg)} B=${hexWord(B, cfg)}`);

    const detail = encBlockDetailed(A, B, S, rounds, cfg);
    A = detail.A;
    B = detail.B;

    log(`→ A=${hexWord(A, cfg)} B=${hexWord(B, cfg)}`, 'val');

    const blockBytes = [
      ...wordToBytes(A, cfg),
      ...wordToBytes(B, cfg)
    ];
    const blockHex = bytesToHex(blockBytes);

    simpleLog(
      `6. Perhitungan matematis blok ${pos / cfg.blockSize + 1}`,
      detail.steps.join('\n\n') +
      `\n\nHasil akhir blok: A=${hexWord(A, cfg)} dan B=${hexWord(B, cfg)}.` +
      `\nA dan B diubah lagi menjadi byte little-endian: [${bytesText(blockBytes)}].` +
      `\nCiphertext blok ${pos / cfg.blockSize + 1}: ${blockHex}`
    );

    cipherBytes.push(...blockBytes);
  }

  const ciphertext = bytesToHex(cipherBytes);
  log(`\nCiphertext: ${ciphertext}`, 'val');
  return ciphertext;
}

function decryptRC5(ciphertext, key, rounds, keyLength, wordSize) {
  logs = [];
  simpleLogs = [];
  log('=== DEKRIPSI RC5 ===', 'step');
  log(`Ciphertext: ${ciphertext}`, 'val');
  simpleLog('1. Ciphertext diterima', `Data yang masuk masih berbentuk hex. Data ini akan dibalik lagi menjadi teks asli memakai kunci dan parameter yang sama.`);

  const expanded = keyExpansion(key, rounds, keyLength, wordSize);
  const S = expanded.S;
  const cfg = expanded.cfg;
  simpleLog('2. Kunci diproses lagi', `Kunci dibuat menjadi sub-key yang sama seperti saat enkripsi. Kalau kunci atau parameternya beda, hasil dekripsi tidak akan cocok.`);
  simpleLog('3. Aturan RC5 dipakai', `Mode yang berjalan adalah RC5-${wordSize}/${rounds}/${keyLength}. Parameter ini harus sama dengan saat proses enkripsi.`);

  const bytes = hexToBytes(ciphertext);
  if (bytes.length % cfg.blockSize !== 0) {
    throw new Error('Panjang ciphertext tidak sesuai ukuran blok RC5.');
  }

  log('\n=== PROSES BLOK ===', 'step');

  const plainBytes = [];

  for (let pos = 0; pos < bytes.length; pos += cfg.blockSize) {
    let A = bytesToWord(bytes, pos, cfg);
    let B = bytesToWord(bytes, pos + cfg.u, cfg);

    log(`Blok ${pos / cfg.blockSize + 1}: A=${hexWord(A, cfg)} B=${hexWord(B, cfg)}`);

    const decrypted = decBlock(A, B, S, rounds, cfg);
    A = decrypted[0];
    B = decrypted[1];

    log(`→ A=${hexWord(A, cfg)} B=${hexWord(B, cfg)}`, 'val');
    simpleLog(`Blok ${pos / cfg.blockSize + 1} dibuka`, `Operasi enkripsi dibalik dari putaran terakhir ke putaran awal. Hasil blok mulai kembali mendekati data asli.`);

    plainBytes.push(...wordToBytes(A, cfg));
    plainBytes.push(...wordToBytes(B, cfg));
  }

  const cleanBytes = unpadBytes(plainBytes, cfg.blockSize);
  const plaintext = bytesToText(cleanBytes);

  log(`\nPlaintext: "${plaintext}"`, 'val');
  return plaintext;
}

/* =========================================================
   Mulai dari sini urusannya ke tampilan web: tombol, input, output, dan log.
   ========================================================= */
function setMode(m) {
  mode = m;
  const enc = m === 'encrypt';

  document.getElementById('btn-enc').className = 'mode-btn' + (enc ? ' active' : '');
  document.getElementById('btn-dec').className = 'mode-btn' + (!enc ? ' active' : '');
  document.getElementById('lbl-input').textContent = enc ? 'Plaintext' : 'Ciphertext (Hex)';
  document.getElementById('lbl-output').textContent = enc ? 'Ciphertext (Hex)' : 'Plaintext';
  document.getElementById('btn-label').textContent = enc ? 'Jalankan Enkripsi' : 'Jalankan Dekripsi';
  document.getElementById('input-text').placeholder = enc ? 'Masukkan teks...' : 'Masukkan ciphertext hex...';
  document.getElementById('output-box').textContent = 'Hasil akan muncul di sini...';
  document.getElementById('output-box').className = 'output-box empty';
  document.getElementById('input-text').value = '';
  document.getElementById('error-msg').textContent = '';
  document.getElementById('log-box').innerHTML = '<span style="color:var(--border2);font-style:italic">— menunggu proses —</span>';
  document.getElementById('simple-log-box').innerHTML = '<span style="color:var(--border2);font-style:italic">— penjelasan mudah akan muncul di sini —</span>';
}

function updateParams() {
  const r = document.getElementById('input-rounds').value;
  const b = document.getElementById('input-keylen').value;
  const w = document.getElementById('input-wordsize').value;

  W = parseInt(w);

  document.getElementById('input-key').maxLength = parseInt(b);
  document.getElementById('param-r').textContent = r;
  document.getElementById('param-w').innerHTML = `${w} <span class="param-unit">bit</span>`;
  document.getElementById('param-b').innerHTML = `${b} <span class="param-unit">byte</span>`;
  document.getElementById('param-mode').textContent = `RC5-${w}/${r}/${b}`;
}

function runRC5() {
  const input = document.getElementById('input-text').value.trim();
  const key = document.getElementById('input-key').value;
  const rounds = parseInt(document.getElementById('input-rounds').value);
  const keyLength = parseInt(document.getElementById('input-keylen').value);
  const wordSize = parseInt(document.getElementById('input-wordsize').value);
  const err = document.getElementById('error-msg');
  const out = document.getElementById('output-box');

  err.textContent = '';

  if (!input) {
    err.textContent = '⚠ Input tidak boleh kosong.';
    return;
  }

  if (!key) {
    err.textContent = '⚠ Kunci tidak boleh kosong.';
    return;
  }

  if (isNaN(rounds) || rounds < 1 || rounds > 255) {
    err.textContent = '⚠ Putaran harus antara 1–255.';
    return;
  }

  if (![16, 32, 64].includes(wordSize)) {
    err.textContent = '⚠ Word size hanya boleh 16, 32, atau 64 bit.';
    return;
  }

  try {
    let result;

    if (mode === 'encrypt') {
      result = encryptRC5(input, key, rounds, keyLength, wordSize);
      out.textContent = result;
      out.className = 'output-box';
    } else {
      const hex = input.replace(/\s/g, '');
      if (!/^[0-9a-fA-F]+$/.test(hex) || hex.length % 2 !== 0) {
        err.textContent = '⚠ Format hex tidak valid.';
        return;
      }
      result = decryptRC5(hex, key, rounds, keyLength, wordSize);
      out.textContent = result;
      out.className = 'output-box plain';
    }

    renderLog();
    renderSimpleLog();
  } catch (e) {
    err.textContent = '⚠ ' + e.message;
  }
}

function renderLog() {
  const box = document.getElementById('log-box');

  box.innerHTML = logs.map(item => {
    if (item.type === 'step') return `<div><span class="log-step">${esc(item.msg)}</span></div>`;
    if (item.type === 'val') return `<div><span class="log-val">${esc(item.msg)}</span></div>`;
    return `<div>${esc(item.msg)}</div>`;
  }).join('');

  box.scrollTop = box.scrollHeight;
}

function renderSimpleLog() {
  const box = document.getElementById('simple-log-box');

  box.innerHTML = simpleLogs.map(item => {
    return `<div class="simple-log-item"><div class="simple-log-title">${esc(item.title)}</div><div class="simple-log-text">${esc(item.text)}</div></div>`;
  }).join('');

  box.scrollTop = box.scrollHeight;
}

function esc(text) {
  return String(text)
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;');
}

function copyOutput() {
  const text = document.getElementById('output-box').textContent;
  if (!text || text === 'Hasil akan muncul di sini...') return;

  navigator.clipboard.writeText(text).then(() => {
    const btn = document.querySelector('.copy-btn');
    btn.textContent = 'Tersalin!';
    setTimeout(() => btn.textContent = 'Salin Hasil', 2000);
  });
}

updateParams();
