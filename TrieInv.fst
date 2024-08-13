module TrieInv

open FStar.Vector
module U32 = FStar.UInt32
module U = FStar.UInt
open Trie
open FStar.Classical.Sugar

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

// --- Insert Lemmas ---

let rec insert0_trie (l:list b_nat) (t:trie0 alphabet_size)
  : Lemma (requires is_trie t) (ensures is_trie (insert0 l t))
  =
  match (t,l) with
  | (L,[]) -> ()
  | (_,[]) -> ()
  | (L,x::xs) -> insert0_trie xs L
  | (N (a, b), x::xs) -> insert0_trie xs (index a (U32.uint_to_t x))

let insert (x:list b_nat) (t:trie) : trie
  =
  insert0_trie x t;
  insert0 x t

// --- Empty array Lemmas ---

// Forward: exists child node ==> not (is_empty a)

let rec del_lem_back2 (a:trie_array)
                      (i':b_nat)
                      (pf:squash (not (is_empty' a i')))
  : Tot (squash (not (is_empty a))) (decreases (U32.v alphabet_size - i'))
  =
  if i' = U32.v alphabet_size - 1
  then pf
  else let pf' : squash (not (is_empty' a (i'+1))) = () in
       del_lem_back2 a (i'+1) pf'

let del_lem_back1 (a:trie_array)
  : Lemma (requires (exists (i:b_nat).
                     N? (index a (U32.uint_to_t i))))
          (ensures not (is_empty a))
  =
  let pf : squash (exists (i': b_nat). not (is_empty' a i')) = () in
  exists_elim
  #_
  #(fun i' -> not (is_empty' a i'))
  #(not (is_empty a))
  pf
  (del_lem_back2 a)

let del_lem_back (a:trie_array)
  : Lemma ((exists (i:b_nat).
                    N? (index a (U32.uint_to_t i)))
           ==>
          (not (is_empty a)))
  =
  implies_intro (exists (i:b_nat).
                         N? (index a (U32.uint_to_t i)))
                (fun pfp -> (not (is_empty a)))
                (fun pfp -> del_lem_back1 a)

// Backward:  exists child node <== not (is_empty a)

let rec del_lem' (a:trie_array) (i:b_nat)
  : Lemma (requires not (is_empty' a i))
          (ensures (exists (i:b_nat).
                            N? (index a (U32.uint_to_t i))))
  =
  if N? (index a (U32.uint_to_t i))
  then ()
  else if i = 0
      then ()
      else del_lem' a (i-1)

let del_lem (a:trie_array)
  : Lemma (requires not (is_empty a))
          (ensures (exists (i:b_nat).
                            N? (index a (U32.uint_to_t i))))
  = del_lem' a (U32.v alphabet_size - 1)

// --- Delete Lemmas ---

let rec delete0_trie (l:list b_nat) (t:trie0 alphabet_size)
  : Lemma (requires is_trie t) (ensures is_trie (delete0 l t))
  =
  match (t,l) with
  | (L,_) -> ()
  | (N (a,_), []) -> if is_empty a then () else del_lem a
  | (N (a,is_t), x::xs) ->
      match index a (U32.uint_to_t x) with
      | L -> ()
      | t' ->
        match delete0 xs t' with
        | L -> let N (a',b') = N (update a (U32.uint_to_t x) L , is_t)
               in if is_empty a' && not is_t
                  then ()
                  else if is_t then () else del_lem a'
        | t'' -> delete0_trie xs t'

let delete (x:list b_nat) (t:trie) : trie
  =
  delete0_trie x t;
  delete0 x t