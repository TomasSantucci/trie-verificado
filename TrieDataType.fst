module TrieDataType

open FStar.Vector
module U32 = FStar.UInt32
module U = FStar.UInt

let alphabet_size : U32.t = U32.uint_to_t 26

// b_nat represents a bounded natural that can fit in 32 bits
type b_nat = x:nat{x < U32.v alphabet_size /\ U.size x 32}

let functio (b_nat) : bool = true

let v : b_nat = 25

noeq
type trie0 (n : U32.t) =
  | L
  | N of raw (trie0 n) n & bool

let index_dec (#a:Type) (l:len_t) (v:raw a l) (i : U32.t{U32.v i < U32.v l})
  : Lemma (index v i << v)
          [SMTPat (index v i)]
  = admit()

let rec is_trie (t:trie0 alphabet_size) : Tot prop
  =
  match t with
  | L -> true
  | N (a,true) ->
    (forall (i:b_nat).
      is_trie (index a (U32.uint_to_t i)))
  | N (a,false) ->
    (forall (i:b_nat).
      is_trie (index a (U32.uint_to_t i)))
    /\
    (exists (i:b_nat).
        N? (index a (U32.uint_to_t i)))

type trie = t:(trie0 alphabet_size){is_trie t}
