module Client.Indexed

open Container.Indexed
open TrieDataType
open Trie

let l1 : list b_nat = [1]
let l2 : list b_nat = [1;2]
let l3 : list b_nat = [1;2;3]
let l4 : list b_nat = [4]

let test #s {| icontainer (list b_nat) s |} () =
  let e : s _ = empty in
  let e = ins l1 e in
  let e = ins l2 e in
  let e = ins l3 e in
  let e = ins l4 e in
  let e = del l2 e in
  assert (mem l1 e);
  assert (not (mem l2 e));
  assert (mem l3 e);
  assert (mem l4 e);
  ()

let test_list () =
  test #_ #(icontainer_from_container (list b_nat) trie
               FStar.Tactics.Typeclasses.solve) ()
