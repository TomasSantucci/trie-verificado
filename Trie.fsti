module Trie

open Container
open TrieDataType

instance val tries_are_containers0 (#alph_size: u32pos)
  : container0 (list (b_nat alph_size)) (trie alph_size)

instance val tries_are_container_laws (#alph_size: u32pos)
  : container_laws (list (b_nat alph_size)) (trie alph_size) tries_are_containers0

instance val tries_are_containers (#alph_size: u32pos)
  : container (list (b_nat alph_size)) (trie alph_size)
