// node splice.js file startMarker endMarker chunkFile : [start, end) を chunk で置き換える
const fs = require('fs');
const [f, a, b, ch] = process.argv.slice(2);
const s = fs.readFileSync(f, 'utf8'); const i = s.indexOf(a), j = s.indexOf(b, i < 0 ? 0 : i);
if (i < 0 || j < 0) { console.error('marker not found', i, j); process.exit(1); }
fs.writeFileSync(f, s.slice(0, i) + fs.readFileSync(ch, 'utf8') + s.slice(j));
