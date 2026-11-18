for (const s of ['p_set','p_order','p_field','p_nat','p_abs','p_ch2','p_ch3','p_ch4','p_more', ...process.argv.slice(2)]) require('./'+s);
const K=require('./kit');console.log(K.proved.length, require('./core').getNodeCount());
