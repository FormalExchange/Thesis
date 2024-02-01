(*Require Import ssreflect ssrbool.
Require Export Lists.List.
Require Export GenReflect SetSpecs.
Require Export DecList.
Require Export DecSort.
Require Export morderorder.
Require Export Quantity.
Require Export mMatching.
Require Export MatchingAlter.
Require Export MQFair.
*)
Require Export Matching.
(*Require Export Quantity.*)

Section Uniqueness.

(*
Definition Optimal_IR_Uniform (M:list transaction)(B:list order)(A:list order): 
matching_in B A M/\ Is_IR M /\ Uniform M/\(forall M', (matching_in B A M'/\Is_IR M' /\ Uniform M') -> QM(M')<=QM(M)).
*)

(* A similar version of this theorem is Q_by_asks_aux_T1_T2 
Lemma less_Q_implies_less_qa (M1 M2: list transaction)(A:list order):
Q_by_asks M1 < Q_by_asks M2 ->
exists a' : order, (In a' A)/\(Qty_bid M1 (id a') < Qty_bid M2 (id a')).
Proof. intros H. unfold Q_by_asks in H. 
apply (Q_by_asks_aux_T1_T2 M1 M2 (fun_ids_ask M1)) in H. revert M1 A. induction M2. intros. unfold Q_by_asks in H. simpl in H.
lia. intros. unfold Q_by_asks in H. unfold fun_ids_ask in H. simpl in H.
destruct (memb (ida a) (ids_ask_aux M2)) eqn:Ha. admit. simpl in H.
destruct (Nat.eqb (ida a) (ida a)) eqn: Haa. admit.
assert(Ha:(ttqa M1 a < ttqa M2 a)\/(ttqa M1 a >= ttqa M2 a)).
lia. destruct Ha. exists a. auto. assert(QMa M1 A < QMa M2 A).
lia. apply IHA in H1. destruct H1. destruct H1. exists x. auto. Qed.

Lemma size_equal_and_gt_imply_lt_ask (M1 M2: list transaction)(A:list order)
(a:order):
(Q_by_asks M1 = Q_by_asks M2) -> In a A -> (ttqa M1 a > ttqa M2 a) -> 
(exists a', (In a' A)/\(ttqa M1 a' < ttqa M2 a')).

Proof. intros. 
       induction A. elim H0. 
       simpl in H0. destruct H0. subst a0.
       simpl in H. assert(HM:QMa M1 A < QMa M2 A).
       lia. apply less_Q_implies_less_qa with (A:=A) in HM.
       destruct HM. destruct H0. exists x. auto.
       simpl in H.
       assert(Ha:(ttqa M1 a0 < ttqa M2 a0)
       \/(ttqa M1 a0 = ttqa M2 a0)
       \/(ttqa M1 a0 > ttqa M2 a0)).
       lia.
       destruct Ha.
       exists a0. auto.
       destruct H2.
       assert(QMa M1 A = QMa M2 A).
       lia. apply IHA in H3.
       destruct H3. destruct H3. exists x. auto.
       auto.
       assert(QMa M1 A < QMa M2 A). lia.
       apply less_Q_implies_less_qa with (A:=A) in H3.
       destruct H3. destruct H3. exists x. auto. Qed.


Lemma Qsize_equal_and_gt_imply_lt_ask (M1 M2: list transaction)(A:list order)
(NDA: NoDup A)(a:order):
(QM(M1) = QM(M2)) -> (ttqa M1 a > ttqa M2 a) -> asks_of M1 [<=] A
-> asks_of M2 [<=] A ->
(exists a', (In a' A)/\(ttqa M1 a' < ttqa M2 a')).
Proof. intros. apply QM_equal_QMa in H1 as H3. apply QM_equal_QMa in H2 as H4.
       rewrite <- H3 in H. rewrite <- H4 in H.
       assert(Ha1:In a (asks_of M1)). apply ttqa_intro1. lia.
       assert (Ha2: In a A). eauto.
       apply size_equal_and_gt_imply_lt_ask with (a:=a). all:auto. Qed. 
*)
       


Theorem completeness_asks (M1 M2: list transaction) (B:list order) (A:list order)
(NDA: NoDup (ids A))(NDt: NoDup (timesof A))(a:order):
  (Matching M1 B A)/\ (Matching M2 B A) 
  /\(Vol(M1) = Vol(M2))
  /\(Is_fair_asks M1 A) /\ (Is_fair_asks M2 A) 
    -> (Qty_ask M1 (id a) = Qty_ask M2 (id a)). 
Proof. unfold Is_fair_asks. intros H. destruct H as [H1 H]. destruct H as [H2 H]. 
destruct H as [H3 H]. destruct H as [H4 H]. 
assert(Hta:(Qty_ask M1 (id a) = Qty_ask M2 (id a))\/(Qty_ask M1 (id a) <> Qty_ask M2 (id a))).
eauto. destruct Hta as [H5 | H5]. auto.
assert(Hga:Qty_ask M1 (id a) > Qty_ask M2 (id a)\/Qty_ask M1 (id a) < Qty_ask M2 (id a)).
lia. destruct Hga as [H6 | H6]. 
  (*Case when there exists an ask a such that it's total trade quantities is more in M1 than M2*)
  { assert(H7:exists a, (In (id a) (ids A))/\(Qty_ask M1 (id a) < Qty_ask M2 (id a))).
    { apply QM1_eq_QM2_extra_ask_in_M1 with (i:=(id a)) in H6 as H1a. 
      destruct H1a as [i H1a]. 
      assert(Hq:Qty_ask M1 (id a) >0). lia.
      apply Qty_positive_extra_ask_in_A  with (B:=B)(A:=A) in Hq.
      destruct Hq as [a1 Hq]. destruct Hq as [Ha1 ida1a].
      assert(Hq:Qty_ask M2 i >0). lia.
      apply Qty_positive_extra_ask_in_A  with (B:=B)(A:=A) in Hq.
      destruct Hq as [a2 Hq]. destruct Hq as [Ha2 ida2a].
      exists a2. split. apply ids_intro. auto. rewrite ida2a. all:auto.
    } assert(Hq:Qty_ask M1 (id a) >0). lia.
      apply Qty_positive_extra_ask_in_A  with (B:=B)(A:=A) in Hq.
      destruct Hq as [a1 Hq]. destruct Hq as [Ha1 ida1a].
      destruct H7 as [a2' H7]. destruct H7 as [H7 H10].
      apply ids_elim in H7. destruct H7 as [a2 H7]. destruct H7 as [H7 H11].
      rewrite <- ida1a in H6. rewrite <- H11 in H10.
      assert(H0:a1 = a2 \/ a1<> a2). eauto. destruct H0 as [H0 | H0]. subst a1. lia. 
      assert(Heq:~eqcompetitive a1 a2). 
      { intro Hn. unfold eqcompetitive in Hn.
        move /andP in Hn. destruct Hn as [Hp Ht]. 
        move /eqP in Ht. apply nodup_timesof_uniq_order with (b1:=a1) in H7.
        auto. all:auto. 
      }
      assert(Ha: (acompetitive a1 a2)\/(acompetitive a2 a1)). 
      apply acompetitive_P. destruct Ha as [Ha | Ha]. 
      { assert(Qty_ask M2 (id a1) = oquantity a1). apply H with (a':=a2).
        split. auto. split. auto.
        split. auto. apply Qty_ask_t_zero_converse. 
        lia. assert (Qty_ask M1 (id a1) <= oquantity a1). apply H1. auto.
        lia.
      }
      { assert(H8:Qty_ask M1 (id a2) = oquantity a2). apply H4 with (a':=a1).
        split. auto. split. auto.
        split. split. auto. unfold eqcompetitive. unfold eqcompetitive in Heq.
        intro. destruct Heq. move /andP in H8. destruct H8 as [H8 H9]. 
        move /eqP in H8. move /eqP in H9. apply /andP. split.
        apply /eqP. auto. apply /eqP. auto. apply Qty_ask_t_zero_converse. 
        lia. assert (Qty_ask M2 (id a2) <= oquantity a2). apply H2. auto.
        lia.
      } auto. }
  (*Case when there exists an ask a such that it's total trade quantities is more in M2 than M1*)
  { assert(H7:exists a, (In (id a) (ids A))/\(Qty_ask M2 (id a) < Qty_ask M1 (id a))).
    { apply QM1_eq_QM2_extra_ask_in_M1 with (i:=(id a)) in H6 as H1a. 
      destruct H1a as [i H1a]. 
      assert(Hq:Qty_ask M2 (id a) >0). lia.
      apply Qty_positive_extra_ask_in_A  with (B:=B)(A:=A) in Hq.
      destruct Hq as [a1 Hq]. destruct Hq as [Ha1 ida1a].
      assert(Hq:Qty_ask M1 i >0). lia.
      apply Qty_positive_extra_ask_in_A  with (B:=B)(A:=A) in Hq.
      destruct Hq as [a2 Hq]. destruct Hq as [Ha2 ida2a].
      exists a2. split. apply ids_intro. auto. rewrite ida2a. all:auto.
    } assert(Hq:Qty_ask M2 (id a) >0). lia.
      apply Qty_positive_extra_ask_in_A  with (B:=B)(A:=A) in Hq.
      destruct Hq as [a1 Hq]. destruct Hq as [Ha1 ida1a].
      destruct H7 as [a2' H7]. destruct H7 as [H7 H10].
      apply ids_elim in H7. destruct H7 as [a2 H7]. destruct H7 as [H7 H11].
      rewrite <- ida1a in H6. rewrite <- H11 in H10.
      assert(H0:a1 = a2 \/ a1<> a2). eauto. destruct H0 as [H0 | H0]. subst a1. lia. 
      assert(Heq:~eqcompetitive a1 a2). 
      { intro Hn. unfold eqcompetitive in Hn.
        move /andP in Hn. destruct Hn as [Hp Ht]. 
        move /eqP in Ht. apply nodup_timesof_uniq_order with (b1:=a1) in H7.
        auto. all:auto.
      }
      assert(Ha: (acompetitive a1 a2)\/(acompetitive a2 a1)). 
      apply acompetitive_P. destruct Ha as [Ha | Ha]. 
      { assert(Qty_ask M1 (id a1) = oquantity a1). apply H4 with (a':=a2).
        split. auto. split.  auto.
        split. auto. apply Qty_ask_t_zero_converse. lia.
        assert (Qty_ask M2 (id a1) <= oquantity a1). apply H2. auto.
        lia.
      }
      { assert(H8:Qty_ask M2 (id a2) = oquantity a2). apply H with (a':=a1).
        split. auto. split.  auto.
        split. split. auto. unfold eqcompetitive. unfold eqcompetitive in Heq.
        intro. destruct Heq. move /andP in H8. destruct H8 as [H8 H9]. 
        move /eqP in H8. move /eqP in H9. apply /andP. split.
        apply /eqP. auto. apply /eqP. auto. apply Qty_ask_t_zero_converse. 
        lia. assert (Qty_ask M1 (id a2) <= oquantity a2). apply H1. auto.
        lia.
      } auto. }
Qed.

Theorem completeness_bids (M1 M2: list transaction) (B:list order) (A:list order)
(NDB: NoDup (ids B))(NDt: NoDup (timesof B))(b:order):
  (Matching M1 B A)/\ (Matching M2 B A) 
  /\(Vol(M1) = Vol(M2))
  /\(Is_fair_bids M1 B) /\ (Is_fair_bids M2 B)
    -> (Qty_bid M1 (id b) = Qty_bid M2 (id b)). 
Proof. (*Same as above. Copy paste and use bid instead of ask. *)
Admitted.


Theorem completeness (M1 M2: list transaction) (B A:list order)
(NDB: NoDup (ids B))(NDA: NoDup (ids A))
(NDtB: NoDup (timesof B))(NDtA: NoDup (timesof A))
(b a:order):
(Matching M1 B A) /\
(Matching M2 B A) /\
(Vol(M1) = Vol(M2)) /\
(Is_fair M1 B A) /\ (Is_fair M2 B A) -> 
(Qty_ask M1 (id a) = Qty_ask M2 (id a))/\
(Qty_bid M1 (id b) = Qty_bid M2 (id b)).
Proof. intros. split.
                { apply completeness_asks with (B:=B)(A:=A). all:auto. 
                  split. apply H. split. apply H. split. apply H. split. apply H. apply H.
                }
                { apply completeness_bids with (B:=B)(A:=A). all:auto. 
                  split. apply H. split. apply H. split. apply H. split. apply H. apply H.
                } Qed.



Lemma soundness_asks (M1 M2: list transaction) (B A:list order)
(NDA: NoDup (ids A)):
(Matching M1 B A)-> (Matching M2 B A) ->
(forall a, (Qty_ask M1 (id a) = Qty_ask M2 (id a)))
->(Is_fair_asks M1 A)  
-> (Is_fair_asks M2 A).
Proof. unfold Is_fair_asks. 
intros. specialize (H1 a') as Hs'.
specialize (H1 a) as Hs.
destruct H3. destruct H4. 
destruct H5. apply ids_ask_intro0 in H6.
rewrite <- Hs' in H6. 
apply Qty_ask_t_zero_converse in H6.
rewrite <- Hs. apply H2 with (a':=a').
auto. Qed.

Lemma soundness_bids (M1 M2: list transaction) (B A:list order)
(NDB: NoDup (ids B)):
(Matching M1 B A)-> (Matching M2 B A) ->
(forall b, (Qty_bid M1 (id b) = Qty_bid M2 (id b)))
->(Is_fair_bids M1 B)  
-> (Is_fair_bids M2 B).
Proof. unfold Is_fair_bids. 
intros. specialize (H1 b') as Hs'.
specialize (H1 b) as Hs.
destruct H3. destruct H4. 
destruct H5. apply ids_bid_intro0 in H6.
rewrite <- Hs' in H6. 
apply Qty_bid_t_zero_converse in H6.
rewrite <- Hs. apply H2 with (b':= b').
auto. Qed.

(* Definition incr (x y : nat) := Nat.leb x y.

Definition stime (L: list order):= Sorted incr (timesof L).
*)


Theorem soundness (M1 M2: list transaction) (B A:list order)
(NDB: NoDup (ids B))(NDA: NoDup (ids A)):
(Matching M1 B A)-> (Matching M2 B A) ->
(forall b, (Qty_bid M1 (id b) = Qty_bid M2 (id b))) ->
(forall a, (Qty_ask M1 (id a) = Qty_ask M2 (id a)))
->(Is_fair M1 B A)  
-> (Is_fair M2 B A).
Proof. intros. destruct H3. split.
                { apply soundness_asks with (B:=B)(A:=A)(M2:=M2) in H2. all:auto. 
                }
                { apply soundness_bids with (B:=B)(A:=A)(M2:=M2) in H4. all:auto.
                } Qed.

End Uniqueness.