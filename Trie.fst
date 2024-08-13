module Trie

open FStar.Vector
module U32 = FStar.UInt32
module U = FStar.UInt

let alphabet_size : U32.t = U32.uint_to_t 26

// b_nat represents a bounded natural that can fit in 32 bits
type b_nat = x:nat{x < U32.v alphabet_size /\ U.size x 32}

noeq
type trie0 (n : U32.t) =
  | L
  | N of raw (trie0 n) n & bool

type trie_array = raw (trie0 alphabet_size) alphabet_size

let empty : trie0 alphabet_size = L

let rec mem (l : list b_nat) (t : trie0 alphabet_size) : Tot bool (decreases l) =
  match t with
  | L -> false
  | N (a, is_t) ->
    match l with
    | [] -> is_t
    | x::xs ->
      match index a (U32.uint_to_t x) with
      | L -> false
      | t' -> mem xs t'

let empty_array : trie_array =
  init alphabet_size (fun _ -> L)

let rec insert0 (l: list b_nat) (t : trie0 alphabet_size) : Tot (trie0 alphabet_size) (decreases l) =
  match (t,l) with
  | (L, []) -> N (empty_array, true)
  | (N (a, _), []) -> N (a, true)
  | (L, x::xs) -> N (init alphabet_size (fun i -> if i = x then insert0 xs L else L), false)
  | (N (a, b), x::xs) ->
    let t' = index a (U32.uint_to_t x) in
    N (update a (U32.uint_to_t x) (insert0 xs t'), b)

let rec is_empty' (a:trie_array) (i:b_nat)
  : Tot bool (decreases i)
= if N? (index a (U32.uint_to_t i))
  then false
  else if i = 0
       then true
       else is_empty' a (i-1)

let is_empty (a:trie_array) : bool
  = is_empty' a ((U32.v alphabet_size) - 1)

let rec delete0 (l: list b_nat) (t : trie0 alphabet_size) : Tot (trie0 alphabet_size) (decreases l) =
  match (t,l) with
  | (L, _) -> L
  | (N (a, _), []) -> if is_empty a then L else N (a,false)
  | (N (a, is_t), x::xs) ->
      match index a (U32.uint_to_t x) with
      | L -> N (a, is_t)
      | t' ->
        match delete0 xs t' with
        | L -> let N (a',b') = N (update a (U32.uint_to_t x) L , is_t)
               in if is_empty a' && not is_t
                  then L
                  else N (a',b')
        | t'' -> N (update a (U32.uint_to_t x) t'', is_t)