module TrieDataType

open FStar.Vector
module U32 = FStar.UInt32
module U = FStar.UInt

// b_nat represents a bounded natural that can fit in 32 bits
type b_nat (alph_size: U32.t) = x: nat{x < U32.v alph_size /\ U.size x 32}

type u32pos = (n: U32.t{U32.v n > 0})

noeq
type trie0 (n: U32.t) =
  | L
  | N of raw (trie0 n) n & bool

let index_dec (#a: Type) (l: len_t) (v: raw a l) (i: U32.t{U32.v i < U32.v l})
  : Lemma (index v i << v)
          [SMTPat (index v i)]
  = admit()

let rec is_trie (#alph_size: u32pos) (t: trie0 alph_size) : Tot prop
  =
  match t with
  | L -> true
  | N (a,true) ->
    (forall (i:b_nat alph_size).
      is_trie (index a (U32.uint_to_t i)))
  | N (a,false) ->
    (forall (i:b_nat alph_size).
      is_trie (index a (U32.uint_to_t i)))
    /\
    (exists (i:b_nat alph_size).
        N? (index a (U32.uint_to_t i)))

type trie (alph_size: u32pos) = t: (trie0 alph_size){is_trie t}
