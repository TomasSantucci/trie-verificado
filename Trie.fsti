module Trie

open Container
open TrieDataType

instance val tries_are_containers0
  : container0 (list b_nat) trie

instance val tries_are_container_laws
  : container_laws (list b_nat) trie tries_are_containers0

instance val tries_are_containers
  : container (list b_nat) trie
