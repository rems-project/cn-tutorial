/*@
datatype char_array {
  Char_array {u64 len, map<u64, u8> chars}
}

function (u64) char_array_len (char_array ca) {
  match ca {
    Char_array { len : l , chars : cs } => { l }
  }
} 

function (u8) char_array_get(char_array ca, u64 i) {
  match ca {
    Char_array { len : l , chars : cs } => { cs[i] }
  }
}

@*/

/*

function map<u64, u8> concat_maps (map<u64, u8> m1, map<u64, u8> m2)
{

}

*/
