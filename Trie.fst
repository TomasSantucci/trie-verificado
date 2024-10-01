module Trie

open FStar.Vector
module U32 = FStar.UInt32
module U = FStar.UInt
open TrieDataType
open FStar.Classical.Sugar
open Container

type trie_array = raw (trie0 alphabet_size) alphabet_size

let empty : trie0 alphabet_size = L

// ==========================
//  Trie Operations
// ==========================

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

// ==========================
//  Operations Lemmas
// ==========================

// ---- insert Lemma ----

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

// ---- is_empty Lemma ----

// -- exists child node ==> not (is_empty a) --

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

// -- exists child node <== not (is_empty a) --

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

// ---- delete Lemma ----

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

// ==========================
//  Tries as containers
// ==========================

let models
  (xs : trie0 alphabet_size)
  (ss : TSet.set (list b_nat))
  : GTot prop
  =
  forall (x: list b_nat).
         mem x xs <==> TSet.mem x ss

let empty_ok_lem (_:unit) : Lemma (models empty TSet.empty)
  = ()

let rec is_empty_lem (t:trie{N? t})
  : squash (exists (l:list b_nat) . mem l t) 
  =
  match t with
  | N (a,true) -> assert(mem [] t)
  | N (a,false) ->
    let pf : squash (exists (i:b_nat).
                             N? (index a (U32.uint_to_t i))) = ()
    in exists_elim
       #b_nat
       #(fun i -> N? (index a (U32.uint_to_t i)))
       #(exists (l:list b_nat) . mem l t)
       pf
       (fun i pfx -> (
                      is_empty_lem (index a (U32.uint_to_t i));
                      assert(exists (l:list b_nat). mem (i::l) t)
                      )
       )

let is_empty_ok (xs:trie)
  : Lemma (models xs TSet.empty <==> L? xs)
  =
  match xs with
  | L -> ()
  | N (_,_) -> is_empty_lem xs

let rec mem_insert (t:trie) (l: list b_nat)
  : Lemma (mem l (insert l t))
  =
  match (t,l) with
  | (_,[]) -> ()
  | (L, x::xs) -> mem_insert t xs
  | (N (a,is_t), x::xs) -> mem_insert (index a (U32.uint_to_t x)) xs

let rec ins_ok_lem1 (t:trie) (l: list b_nat) (l':(list b_nat){mem l' t})
  : Tot (squash (mem l' (insert l t))) (decreases l')
  =
  match (t,l,l') with
  | (_,_,[]) -> ()
  | (_,[],_) -> ()
  | (L,_,_) -> ()
  | (N (a,b), x::xs, y::ys) ->
    if x = y
    then (
          match index a (U32.uint_to_t x) with
          | L -> ()
          | t' -> ins_ok_lem1 t' xs ys
         )
    else ()

let rec ins_ok_lem2 (t:trie) (l: list b_nat) (l':(list b_nat){not (mem l' t) /\ (l <> l')})
  : Tot (squash (not (mem l' (insert l t)))) (decreases l')
  =
  match (t,l,l') with
  | (_,_,[]) -> ()
  | (_,[],_) -> ()
  | (L, x::xs, y::ys) ->
    if x = y then ins_ok_lem2 L xs ys else ()
  | (N (a, b), x::xs, y::ys) ->
    if x = y
    then ins_ok_lem2 (index a (U32.uint_to_t x)) xs ys
    else ()

let ins_ok_lem (x:list b_nat) (xs:trie) (ss : TSet.set (list b_nat))
  : Lemma (requires xs `models` ss)
          (ensures  insert x xs
                     `models`
                    TSet.union ss (TSet.singleton x))
  =
  mem_insert xs x;

  forall_intro (l:(list b_nat){mem l xs})
               (fun l' -> mem l' (insert x xs))
               (ins_ok_lem1 xs x);

  forall_intro (l:(list b_nat){not (mem l xs) /\ (l <> x)})
               (fun l' -> not (mem l' (insert x xs)))
               (ins_ok_lem2 xs x)

let rec mem_delete (t:trie) (l:list b_nat)
  : Lemma (not (mem l (delete l t)))
  =
  match (t,l) with
  | (L,_) -> ()
  | (_,[]) -> ()
  | (N (a,b), x::xs) ->
      match index a (U32.uint_to_t x) with
      | L -> ()
      | t' ->
        match delete0 xs t' with
        | L -> ()
        | t'' -> mem_delete t' xs

let rec del_ok_lem1 (t:trie) (l:list b_nat) (l':(list b_nat){not (mem l' t)})
  : Tot (squash (not (mem l' (delete l t))))
  =
  match (t,l,l') with
  | (L,_,_) -> ()
  | (N(_,_),_,[]) -> ()
  | (N(_,_),[],_) -> ()
  | (N (a,_), x::xs, y::ys) -> 
    if x = y
    then (
          match index a (U32.uint_to_t x) with
          | L -> ()
          | t' ->
            match delete0 xs t' with
            | L -> ()
            | t'' -> del_ok_lem1 t' xs ys
         )
    else ()

let del_ok_lem2' (t:trie{N? t}) (l:(list b_nat){Cons? l})
  : Lemma (requires (let N (a,_) = t in is_empty a))
          (ensures not (mem l t))
  =
  match (t,l) with
  | (N (a,_),_) -> del_lem_back a

let rec del_ok_lem2 (t:trie) (l:list b_nat) (l':(list b_nat){(mem l' t) /\ (l <> l')})
  : Tot (squash (mem l' (delete l t)))
  =
  match (t,l,l') with
  | (L,_,_) -> ()
  | (N(_,_),_,[]) -> ()

  | (N(a,_),[],x::xs) ->
    if is_empty a
    then del_ok_lem2' t l'
    else ()

  | (N (a, is_t), x::xs, y::ys) -> 
    if x = y
    then (
          match index a (U32.uint_to_t x) with
          | L -> ()
          | t' -> del_ok_lem2 t' xs ys
         )
    else (
          match index a (U32.uint_to_t x) with
          | L -> ()
          | t' -> del_lem_back (update a (U32.uint_to_t x) L)
         )

let del_ok_lem (x:list b_nat) (t:trie) (ss: TSet.set (list b_nat))
  : Lemma (requires t `models` ss)
          (ensures delete x t
                   `models`
                   TSet.intersect ss (TSet.complement <| TSet.singleton x))
  =
  mem_delete t x;

  //assume(forall (l:(list b_nat){not (mem t l)}). not (mem (delete x t) l));
  forall_intro (l:(list b_nat){not (mem l t)})
               (fun l' -> not (mem l' (delete x t)))
               (del_ok_lem1 t x);
  
  //assume(forall (l:(list b_nat){(mem t l) /\ (l <> x)}). (mem (delete x t) l));
  forall_intro (l:(list b_nat){(mem l t) /\ (l <> x)})
               (fun l' -> mem l' (delete x t))
               (del_ok_lem2 t x)

instance tries_are_containers0
  : container0 (list b_nat) trie = {
    empty = L;
    is_empty = L?;

    mem = mem;
    ins = insert;
    del = delete;
  }

instance tries_are_container_laws
  : container_laws (list b_nat) trie tries_are_containers0 = {
    models = models;
    empty_ok = empty_ok_lem;
    is_empty_ok = is_empty_ok;
    mem_ok = (fun _ _ _ -> ());
    ins_ok = ins_ok_lem;
    del_ok = del_ok_lem;
}

instance tries_are_containers
  : container (list b_nat) trie = {
    ops = tries_are_containers0;
    laws = tries_are_container_laws;
  }
