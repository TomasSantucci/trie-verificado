module Trie

open FStar.Vector
module U32 = FStar.UInt32
module U = FStar.UInt

let alphabet_size : U32.t = U32.uint_to_t 26

type b_nat = x:nat{x < U32.v alphabet_size /\ U.size x 32}

noeq
type trie0 (n : U32.t) =
  | L
  | N of raw (trie0 n) n & bool & int

let rec mem (t : trie0 alphabet_size) (l : list b_nat) : Tot bool (decreases l) =
  match t with
  | L -> false
  | N (a, is_t, _) ->
    match l with
    | [] -> is_t
    | x::xs ->
      match index a (U32.uint_to_t x) with
      | L -> false
      | t' -> mem t' xs

let empty_array : raw (trie0 alphabet_size) alphabet_size =
  init alphabet_size (fun _ -> L)

let rec insert0 (t : trie0 alphabet_size) (l: list b_nat) : Tot (trie0 alphabet_size) (decreases l) =
  match (t,l) with
  | (L, []) -> N (empty_array, true, 0)
  | (N (a, _, n), []) -> N (a, true, n)
  | (L, x::xs) -> N (init alphabet_size (fun i -> if i = x then insert0 L xs else L), false, 1)
  | (N (a, b, n), x::xs) ->
    match index a (U32.uint_to_t x) with
    | L -> N (update a (U32.uint_to_t x) (insert0 L xs), b, n + 1)
    | t' -> N (update a (U32.uint_to_t x) (insert0 t' xs), b, n)

let rec delete0 (t : trie0 alphabet_size) (l: list b_nat) : Tot (trie0 alphabet_size) (decreases l) =
  match (t,l) with
  | (L, _) -> L
  | (N (_, _, 0), []) -> L
  | (N (a, _, n), []) -> N (a, false, n)
  | (N (a, is_t, n), x::xs) ->
      match index a (U32.uint_to_t x) with
      | L -> N (a, is_t, n)
      | t' ->
        match delete0 t' xs with
        | L -> if n = 1 && not is_t
               then L
               else N (update a (U32.uint_to_t x) L , is_t, n-1)
        | t'' -> N (update a (U32.uint_to_t x) t'', is_t, n)
