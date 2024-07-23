module TrieProps

open FStar.Vector
module U32 = FStar.UInt32
module U = FStar.UInt
open Trie
open TrieInv
open FStar.Classical.Sugar

let models
  (xs : trie0 alphabet_size)
  (ss : TSet.set (list b_nat))
  : GTot prop
  =
  forall (x: list b_nat).
         mem xs x <==> TSet.mem x ss

let empty_ok_lem (_:unit) : Lemma (models empty TSet.empty)
  = ()

let rec is_empty_lem (t:trie{N? t})
  : squash (exists (l:list b_nat) . mem t l) 
  =
  match t with
  | N (a,true) -> assert(mem t [])
  | N (a,false) ->
    let pf : squash (exists (i:nat{i < U32.v alphabet_size}).
                             N? (index a (U32.uint_to_t i))) = ()
    in exists_elim
       #(i:nat{i < U32.v alphabet_size})
       #(fun i -> N? (index a (U32.uint_to_t i)))
       #(exists (l:list b_nat) . mem t l)
       pf
       (fun i pfx -> (
                      is_empty_lem (index a (U32.uint_to_t i));
                      assert(exists (l:list b_nat). mem t (i::l))
                      )
       )

let is_empty_ok (#a:eqtype) (xs:trie)
  : Lemma (models xs TSet.empty <==> L? xs)
  =
  match xs with
  | L -> ()
  | N (_,_) -> is_empty_lem xs

let rec mem_insert (t:trie) (l: list b_nat)
  : Lemma (mem (insert l t) l)
  =
  match (t,l) with
  | (_,[]) -> ()
  | (L, x::xs) -> mem_insert t xs
  | (N (a,is_t), x::xs) -> mem_insert (index a (U32.uint_to_t x)) xs

let rec ins_ok_lem1 (t:trie) (l: list b_nat) (l':(list b_nat){mem t l'})
  : Tot (squash (mem (insert l t) l')) (decreases l')
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

let rec ins_ok_lem2 (t:trie) (l: list b_nat) (l':(list b_nat){not (mem t l') /\ (l <> l')})
  : Tot (squash (not (mem (insert l t) l'))) (decreases l')
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

  forall_intro (l:(list b_nat){mem xs l})
               (fun l' -> mem (insert x xs) l')
               (ins_ok_lem1 xs x);

  forall_intro (l:(list b_nat){not (mem xs l) /\ (l <> x)})
               (fun l' -> not (mem (insert x xs) l'))
               (ins_ok_lem2 xs x)

let rec mem_delete (t:trie) (l:list b_nat)
  : Lemma (not (mem (delete l t) l))
  =
  match (t,l) with
  | (L,_) -> ()
  | (_,[]) -> ()
  | (N (a,b), x::xs) ->
      match index a (U32.uint_to_t x) with
      | L -> ()
      | t' ->
        match delete0 t' xs with
        | L -> ()
        | t'' -> mem_delete t' xs

let rec del_ok_lem1 (t:trie) (l:list b_nat) (l':(list b_nat){not (mem t l')})
  : Tot (squash (not (mem (delete l t) l')))
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
            match delete0 t' xs with
            | L -> ()
            | t'' -> del_ok_lem1 t' xs ys
         )
    else ()

let del_ok_lem2' (t:trie{N? t}) (l:(list b_nat){Cons? l})
  : Lemma (requires (let N (a,_) = t in is_empty a))
          (ensures not (mem t l))
  =
  match (t,l) with
  | (N (a,_),_) -> del_lem_back_neg a

let rec del_ok_lem2 (t:trie) (l:list b_nat) (l':(list b_nat){(mem t l') /\ (l <> l')})
  : Tot (squash (mem (delete l t) l'))
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
  forall_intro (l:(list b_nat){not (mem t l)})
               (fun l' -> not (mem (delete x t) l'))
               (del_ok_lem1 t x);
  
  //assume(forall (l:(list b_nat){(mem t l) /\ (l <> x)}). (mem (delete x t) l));
  forall_intro (l:(list b_nat){(mem t l) /\ (l <> x)})
               (fun l' -> mem (delete x t) l')
               (del_ok_lem2 t x)