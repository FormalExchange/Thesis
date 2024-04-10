(* This file contains inportant theorems from thesis *)
Require Import Definitions Properties MaxMatch UniqueMatch Programs.

Section Demo.
Notation "s === t" := (perm s t) (at level 80, no associativity).


Theorem Maximum_Maching (Process: list order->list order -> instruction ->
(list order)*(list order)*(list transaction))(B A hat_B hat_A : list order)(tau:instruction):
let B' := (fst (Absorb B A tau)) in
let A' := (snd (Absorb B A tau)) in
let hat_B := (Blist (Process B A tau)) in
let hat_A := (Alist (Process B A tau)) in
let M := (Mlist (Process B A tau)) in

Condition1 M B A hat_B hat_A tau->

Condition3a M B A tau->
Condition3b M B A hat_B tau ->
Condition3c M B A hat_A tau ->

not (matchable B A) ->

NoDup (ids B') ->
NoDup (ids A') ->

MaxMatch (Mlist (Process B A tau)) B' A'.
Proof. apply Maximum_Maching. all:auto. Qed.


Theorem Local_uniqueness 
(Process1 Process2: list order->list order -> instruction->
(list order)*(list order)*(list transaction))
(B1 B2 A1 A2 : list order)(tau:instruction):
B1 === B2 -> A1 === A2 ->
Legal_input B1 A1 tau ->
Properties Process1 -> Properties Process2 ->

(cform (Mlist (Process1 B1 A1 tau))) === (cform (Mlist (Process2 B2 A2 tau))) /\
(Blist (Process1 B1 A1 tau)) === (Blist (Process2 B2 A2 tau))/\
(Alist (Process1 B1 A1 tau)) === (Alist (Process2 B2 A2 tau)).
Proof. intros. eapply Local_uniqueness in H1. split. apply H1. split. apply H1. apply H1. all:auto. Qed.


Theorem global_unique (P1 P2 :(list order)->(list order) -> instruction -> (list order)*(list order)*(list transaction))(I : list instruction)(k:nat):
(Properties P1) /\(Properties P2) /\ structured I  ->
(cform (Mlist (iterated P1 I k))) === (cform (Mlist (iterated P2 I k)))/\
(Blist (iterated P1 I k)) === (Blist (iterated P2 I k)) /\
(Alist (iterated P1 I k)) === (Alist (iterated P2 I k)).
Proof. apply global_unique. Qed.

Theorem Process_correct :
Properties Process_instruction.
Proof. apply Process_correct. Qed.

End Demo.

