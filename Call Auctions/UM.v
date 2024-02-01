Require Export MatchingAlter.

Section UM.


Definition Is_optimal_uniform (M : list transaction)(B: list order)(A: list order) :=
  Is_uniform M B A /\ 
  (forall M': list transaction, Is_uniform M' B A -> Vol(M') <= Vol(M)).

(*Move this function into other file *)
Fixpoint Assign_Transaction_Price (n:nat) (l:list transaction):=
  match l with
  |nil=>nil
  |m::l'=> (Mk_transaction (idb m)  (ida m) n (tquantity m) (tquantity_cond m))::(Assign_Transaction_Price n l')
  end.

(*Move this lemma into other file *)
Lemma Assign_Transaction_Price_is_uniform (l: list transaction)(n:nat):
  uniform (map tprice (Assign_Transaction_Price n l )).
Proof. induction l. simpl.  constructor. simpl. 
         case l eqn: H. simpl.  constructor. simpl. simpl in IHl. constructor;auto. Qed.
(*Move this lemma into other file *)
Lemma last_column_is_trade_price (l:list transaction)(m:transaction)(n:nat): In m (Assign_Transaction_Price n l)->
                                                                  (tprice m = n).
Proof. { intro H. induction l. auto. inversion H as [H0 |].  
         inversion H0 as [H1 ]. simpl. exact. apply IHl in H0. exact. } Qed.
(*Move this lemma into other file *)

Lemma Assign_Transaction_Price_elim (l: list transaction)(n:nat): 
forall m', In m' (Assign_Transaction_Price n l)-> exists m, In m l /\ idb m = idb m' /\ ida m = ida m'. 
  Proof. intros. { induction l. 
           { simpl in H. inversion H. }
           { simpl in H. destruct H.
             {  exists a. split. auto. split. subst m'. simpl. auto. subst m'. simpl. auto. }
             { apply IHl in H as H1. destruct H1 as [m H1]. exists m. 
               destruct H1 as [H2 H1]. destruct H1 as [H3 H1]. split.
               auto. split;auto. } } } Qed.
 
(*Move this lemma into other file *)
Lemma Assign_Transaction_Price_elim_bid (l: list transaction)(n:nat) (m:transaction):
In m (Assign_Transaction_Price n l) -> In (idb m) (map idb l).
Proof. { induction l. intros. simpl. destruct H.
         intros. simpl in H. simpl. destruct H. left. 
         simpl in H. subst m. simpl. exact. right. apply IHl. exact. } Qed.
(*Move this lemma into other file *)
Lemma Assign_Transaction_Price_elim_ask (l: list transaction)(n:nat) (m:transaction):
In m (Assign_Transaction_Price n l) -> In (ida m) (map ida l).
Proof. { induction l. intros. simpl. destruct H.
         intros. simpl in H. simpl. destruct H. left. 
         simpl in H. subst m. simpl. exact. right. apply IHl. exact. } Qed.
 (*Move this lemma into other file *)
Lemma Assign_Transaction_Price_bids (l: list transaction)(n:nat):
(map idb l) = (map idb (Assign_Transaction_Price n l)).
  Proof. { induction l. 
           { simpl. auto. }
           { simpl. f_equal. auto. } } Qed. 

(*Move this lemma into other file *)
Lemma Assign_Transaction_Price_asks (l: list transaction)(n:nat):
  (map ida l) = (map ida (Assign_Transaction_Price n l)).
  Proof. { induction l. 
           { simpl. auto. }
           { simpl. f_equal. auto. } } Qed. 

(*Move this lemma into other file *)
Lemma Assign_Transaction_Price_Qty_bid (l: list transaction)(b:order)(n:nat):
Qty_bid l (id b) = Qty_bid (Assign_Transaction_Price n l) (id b).
Proof. induction l. simpl. auto. simpl. 
       destruct (Nat.eqb (idb a) (id b)) eqn:Hba. lia. lia. Qed.
       
(*Move this lemma into other file *)
Lemma Assign_Transaction_Price_Qty_ask (l: list transaction)(a:order)(n:nat):
Qty_ask l (id a) = Qty_ask (Assign_Transaction_Price n l) (id a).
Proof. induction l. simpl. auto. simpl. 
       destruct (Nat.eqb (ida a0) (id a)) eqn:Haa0. lia. lia. Qed.

(*Move this lemma into other file *)
Lemma Assign_Transaction_Price_size (l: list transaction)(n:nat):
Vol(l) = Vol((Assign_Transaction_Price n l)).
Proof. induction l. simpl. auto.
simpl. lia. Qed.

Lemma Assign_Transaction_Price_fairA (M: list transaction)(A: list order)(n:nat):
Is_fair_asks M A -> Is_fair_asks ((Assign_Transaction_Price n M)) A.
Proof. unfold Is_fair_asks. intros. rewrite <- Assign_Transaction_Price_Qty_ask. apply H with (a:=a)(a':=a'). split. apply H0. split. apply H0. split. apply H0. replace ((ids_ask_aux M)) with (map ida M). rewrite (Assign_Transaction_Price_asks _ n). replace ((map ida (Assign_Transaction_Price n M))) with (ids_ask_aux (Assign_Transaction_Price n M)). apply H0. eauto. eauto. Qed.

Lemma Assign_Transaction_Price_fairB (M: list transaction)(B: list order)(n:nat):
Is_fair_bids M B -> Is_fair_bids ((Assign_Transaction_Price n M)) B.
Proof. unfold Is_fair_bids. intros. rewrite <- Assign_Transaction_Price_Qty_bid. apply H with (b:=b)(b':=b'). split. apply H0. split. apply H0. split. apply H0. replace ((ids_bid_aux M)) with (map idb M). rewrite (Assign_Transaction_Price_bids _ n). replace ((map idb (Assign_Transaction_Price n M))) with (ids_bid_aux (Assign_Transaction_Price n M )). apply H0. eauto. eauto. Qed.

Definition UM_aux B A:=
(Match (Decr_Bid.sort B) (Incr_Ask.sort A)).

Lemma UM_aux_Matching B A:
NoDup (ids B) -> NoDup (ids A) -> Matching (UM_aux B A) B A.
Proof. unfold UM_aux. intros. assert(perm (Decr_Bid.sort B) B). apply SortB_perm. 
assert(perm (Incr_Ask.sort A) A). apply SortA_perm. eapply Maching_permutation.
exact H1. exact H2. apply Match_Matching. apply SortA_NoDup. auto. apply SortB_NoDup. auto.  Qed.


Definition t0:= Mk_transaction 0 0 0 1 not1.

Definition Last_Transaction_Price M:= tprice ((last M t0)).

(*Definition Assign_Transaction_Price p M := replace_column M p.*)

Definition UM B A:= 
           let B:= (Decr_Bid.sort B) in
           let A:= (Incr_Ask.sort A) in
           let M:= (Match B A) in
           let p:= Last_Transaction_Price M in
           Assign_Transaction_Price p M.



Theorem UM_Fair (B:list order)(A:list order)
(NDB: NoDup (ids B))(NDA: NoDup (ids A))(NDBt: NoDup (timesof B))(NDAt: NoDup (timesof A)):
Sorted bcompetitive B -> Sorted acompetitive (A) -> Is_fair (UM B A) B A.
Proof. intros. unfold Is_fair.
               split.
                 { unfold UM. apply Assign_Transaction_Price_fairA. replace (Decr_Bid.sort B) with B. replace (Incr_Ask.sort A) with A. apply Match_Fair_ask. all:auto. rewrite <- Sorted_sortA.  all:auto. 
rewrite <- Sorted_sortB.  all:auto.
}
                 { unfold UM. apply Assign_Transaction_Price_fairB. unfold UM. replace (Decr_Bid.sort B) with B. replace (Incr_Ask.sort A) with A. apply Match_Fair_bid. all:auto. rewrite <- Sorted_sortA.  all:auto.
rewrite <- Sorted_sortB.  all:auto.  } Qed.



Lemma exists_opt_k (B:list order)(A:list order)(b:order)(a:order):
Sorted bcompetitive (b::B) -> 
Sorted acompetitive (a::A) -> 
(forall k M,
(Is_uniform M (b::B) (a::A)) -> 
oprice b >= oprice a ->
Vol(M)>=(min (oquantity b) (oquantity a)) -> 
(Qty_ask M (id a)) >= (min (oquantity b) (oquantity a))/\
(Qty_bid M (id b)) >= (min (oquantity b) (oquantity a))/\
((min (oquantity b) (oquantity a)) - Qty M (id b) (id a) = k) ->
(exists M0, (Is_uniform M0 (b::B) (a::A))/\
((min (oquantity b) (oquantity a)) - Qty M0 (id b) (id a) = 0)/\
Vol(M)=Vol(M0))).
Proof. revert B A b a. induction k. 
       { intros M Uni_M price_ab HvM HQa. exists M. split;auto. split;auto.
         apply HQa. }
       { intros M Uni_M price_ab HvM HQa. destruct HQa as [HQa HQb].
          destruct HQb as [HQb k_n].    (*Main induction case*)
          case (Nat.leb (oquantity b) (oquantity a)) eqn:Hab.
          { assert ((min (oquantity b) (oquantity a)) = oquantity b). 
            eapply min_l. move /leP in Hab;lia.
            assert(Qty M (id b) (id a) < (oquantity b)). lia.
            rewrite H1 in k_n.
            rewrite H1 in HQa. rewrite H1 in HQb. rewrite H1.
            assert(Qty M (id b) (id a) < Qty_bid M (id b)). lia.
            apply Qty_lt_Qty_bid_m_exists in H3.
            assert(Qty M (id b) (id a) < Qty_ask M (id a)). lia.
            apply Qty_lt_Qty_ask_m_exists in H4.
            destruct H3 as [m1 H3]. destruct H4 as [m2 H4]. destruct H3. destruct H5. destruct H4.
            destruct H7.  apply increase_ab_quantity_Is_uniform with (m1:=m1)(m2:=m2) in Uni_M.
            apply IHk in Uni_M. destruct Uni_M as [M0 Uni_M]. destruct Uni_M as [U1 U2].
            destruct U2 as [U2 U3]. exists M0. split. auto. split. rewrite <- H1. auto.
            auto. rewrite (increase_ab_quantity_Vol _ m1 m2 b a). all:auto.  intro.
            subst m1. lia. rewrite <- (increase_ab_quantity_Vol _ m1 m2 b a). all:auto. 
            intro;subst m1;lia. split. 
            rewrite (increase_ab_quantity_Qty_ask _ m1 m2 b a). all:auto. intro;subst m1;lia. lia. 
            split. rewrite (increase_ab_quantity_Qty_bid _ m1 m2 b b a). all:auto. intro;subst m1;lia. lia.
            rewrite (increase_ab_quantity_extra _ m1 m2 b a). all:auto. intro;subst m1;lia. lia. intro;subst m1;lia.
          }
          { assert ((min (oquantity b) (oquantity a)) = oquantity a). 
            eapply min_r. move /leP in Hab;lia.
            assert(Qty M (id b) (id a) < (oquantity a)). lia.
            rewrite H1 in k_n.
            rewrite H1 in HQa. rewrite H1 in HQb. rewrite H1.
            assert(Qty M (id b) (id a) < Qty_bid M (id b)). lia.
            apply Qty_lt_Qty_bid_m_exists in H3.
            assert(Qty M (id b) (id a) < Qty_ask M (id a)). lia.
            apply Qty_lt_Qty_ask_m_exists in H4.
            destruct H3 as [m1 H3]. destruct H4 as [m2 H4]. destruct H3. destruct H5. destruct H4.
            destruct H7.  apply increase_ab_quantity_Is_uniform with (m1:=m1)(m2:=m2) in Uni_M.
            apply IHk in Uni_M. destruct Uni_M as [M0 Uni_M]. destruct Uni_M as [U1 U2].
            destruct U2 as [U2 U3]. exists M0. split. auto. split. rewrite <- H1. auto.
            auto. rewrite (increase_ab_quantity_Vol _ m1 m2 b a). all:auto.  intro.
            subst m1. lia. rewrite <- (increase_ab_quantity_Vol _ m1 m2 b a). all:auto. 
            intro;subst m1;lia. split. 
            rewrite (increase_ab_quantity_Qty_ask _ m1 m2 b a). all:auto. intro;subst m1;lia. lia. 
            split. rewrite (increase_ab_quantity_Qty_bid _ m1 m2 b b a). all:auto. intro;subst m1;lia. lia.
            rewrite (increase_ab_quantity_extra _ m1 m2 b a). all:auto. intro;subst m1;lia. lia. intro;subst m1;lia.
          } } Qed.
(*
Lemma exists_opt (B:list order)(A:list order)(M:list transaction)(b:order)(a:order)
(NZT: forall m : transaction, In m M -> tq m > 0)
(NZA:(forall a0, In a0 (a::A) -> (sq a0) > 0))
(NZB:(forall b0, In b0 (b :: B) -> bq b0 > 0))
(NDA:NoDup (idas_of (a::A)))(NDB:NoDup (idbs_of (b::B))):
Sorted by_dbp (b::B) -> 
Sorted by_sp (a::A) -> 
(Is_uniform M (b::B) (a::A)) -> 
b>=a ->
QM(M)>=(min (bq b) (sq a)) ->
(exists OPT, (Is_uniform OPT (b::B) (a::A))/\
(ttq_ab OPT b a = min (bq b) (sq a))/\QM(M)=QM(OPT)/\
(forall m : transaction, In m OPT -> tq m > 0)).
Proof. intros. 
       assert((exists M', (Is_uniform M' (b::B) (a::A))/\
       (ttqa M' a >= min (bq b) (sq a))/\
       (ttqb M' b >= min (bq b) (sq a))/\QM(M)=QM(M')
       /\forall m : transaction, In m M' -> tq m > 0)).
       eapply exists_ttq_top. all:auto. destruct H4 as [M0 H5].
       destruct H5. destruct H5. destruct H6. 
       destruct (Nat.min (bq b) (sq a) - ttq_ab M0 b a) eqn:Hk.
       {
         eapply exists_opt_k with (k:=0)(A:=A)(a:=a)(B:=B)(b:=b) in H5.
         destruct H5 as [OPT H5]. exists OPT. 
         destruct H5. destruct H7.
         split. apply H5. split. 
         assert (Hmin:ttq_ab OPT b a <= Nat.min (bq b) (sq a)).
         eapply matching_in_elim9 with (B:=(b::B))(A:=(a::A)).
         apply H5.  all:auto.  lia. split. lia. apply H8. lia. apply H7.
       }  
       { assert(Haba:ttqa M0 a >=ttq_ab M0 b a).
         eauto. 
         eapply exists_opt_k with (k:= S n)(A:=A)(a:=a)(B:=B)(b:=b) in H5.
         destruct H5 as [OPT H5]. exists OPT. 
         destruct H5. destruct H7.
         split. apply H5. split. 
         assert (Hmin:ttq_ab OPT b a <= Nat.min (bq b) (sq a)).
         eapply matching_in_elim9 with (B:=(b::B))(A:=(a::A)).
         apply H5.  all:auto.  lia. split. lia. apply H8. lia. apply H7.       }
Qed. 





Lemma unmatchableAB_nil (B:list order) (A:list order) (b:order)(a:order)
(M:list transaction): Sorted by_dbp (b::B) -> Sorted by_sp (a::A) ->
matching_in (b::B) (a::A) M -> b<a-> M=nil.
Proof. { intros H1 H2 H3 H4.
         case M as [|f  M'] eqn:HM.
         { auto. }
         { set (b0:= bid_of f). set (a0:= ask_of f).
           assert (Hfask: In (ask_of f) (a::A)). 
           { eapply matching_in_elim5. exact H3. }
           assert (Hfbid: In (bid_of f) (b::B)). 
           { eapply matching_in_elim4.  exact H3. }
           assert (Hmatch: bid_of f >= ask_of f). eauto.
           assert (h1: by_dbp b b0). 
           { unfold b0. unfold is_true. apply bool_fun_equal.
             intro. exact is_true_true. intro.
              eapply Sorted_elim2. exact by_dbp_refl.
            exact H1. exact Hfbid. }
           assert (h2: by_sp a a0).
           { apply Sorted_elim2 with (x:=a0) in H2.
             auto. apply by_sp_refl. eauto.
           }
           unfold by_dbp in h1. 
           move /orP in h1.
           unfold by_sp in h2. 
           move /orP in h2.
           destruct h1;destruct h2. 
           {
           move /leP in H.
           move /leP in H0.
           unfold b0 in H.
           unfold a0 in H0.
           lia.
           }
           {
           move /leP in H.
           move /andP in H0. destruct H0.
           move /eqP in H0.
           unfold b0 in H.
           unfold a0 in H0.
           lia.
           }
           {
           move /leP in H0.
           move /andP in H. destruct H.
           move /eqP in H.
           unfold b0 in H.
           unfold a0 in H0.
           lia.
           }
           {
           move /andP in H. destruct H.
           move /eqP in H.
           move /andP in H0. destruct H0.
           move /eqP in H0. 
           unfold b0 in H.
           unfold a0 in H0.
           lia.
           }            
 } } Qed.

*)


Lemma exists_opt (B:list order)(A:list order)(M:list transaction)(b:order)(a:order):
NoDup (ids (a::A)) -> NoDup (ids (b::B)) ->
Sorted bcompetitive (b::B) -> 
Sorted acompetitive (a::A) -> 
(Is_uniform M (b::B) (a::A)) -> 
oprice b >= oprice a ->
Vol(M)>=(min (oquantity b) (oquantity a)) -> 
(exists OPT, (Is_uniform OPT (b::B) (a::A))/\
(Qty OPT (id b) (id a) = (min (oquantity b) (oquantity a)))/\
Vol(M)=Vol(OPT)).
Proof. intros. destruct ((min (oquantity b) (oquantity a)) - Qty M (id b) (id a)) eqn:Hk.
exists M. split. auto. split. admit. auto. 
apply exists_opt_k with (M:=M)(A:=A)(B:=B)(k:=S n)(b:=b)(a:=a) in H1.
destruct H1 as [M0 H1]. destruct H1. destruct H6. exists M0. split. auto.
split. admit. all:auto. split. admit. split. admit. auto. Admitted. (*Use Qty_le_Qty_bid to clear admits *)


(*Main Lemma: first prove this.*)
Lemma Match_OPT (B:list order)(A:list order)(M:list transaction):
(NoDup (ids A)) -> (NoDup (ids B)) ->
Sorted bcompetitive B -> 
Sorted acompetitive A -> 
Is_uniform M B A -> Vol(M) <= Vol(Match B A).
Proof. revert M. apply Match_elim. 
- firstorder. unfold Tvalid in H4. unfold valid in H4. induction M as [|t M]. simpl.
auto. assert(In t (t::M)). simpl;auto. apply H4 in H7. destruct H7. destruct H7.
firstorder.
- firstorder. unfold Tvalid in H4. unfold valid in H4. induction M as [|t M]. simpl.
auto. assert(In t (t::M)). simpl;auto. apply H4 in H7. firstorder.
- intros.
assert(HaS: forall x, In x A0 -> (acompetitive a x)). apply Sorted_ointroA_tight. auto.
assert(HbS: forall x, In x B0 -> (bcompetitive b x)). apply Sorted_ointroB_tight. auto.
destruct H7 as [Hu Hm]. unfold Uniform in Hu. 
destruct (PeanoNat.Nat.eqb (oprice a - oprice b) 0) eqn:price.
{ destruct (Compare_dec.lt_eq_lt_dec (oquantity a) (oquantity b)) eqn:f1. 
  { destruct s eqn:f2.
    { specialize (H s). specialize (H l). simpl. 
      destruct (Nat.leb (Vol(M)) (min (oquantity b) (oquantity a))) eqn:Hqab.
      { move /leP in Hqab. 
        replace (Nat.min (oquantity b) (oquantity a)) with (oquantity a) in Hqab. 
        lia. lia. }
      { move /leP in Hqab. assert(Hv:Vol M >= Nat.min (oquantity b) (oquantity a)). lia.
        apply (exists_opt B0 A0 _ _ _) in Hv. all:auto. destruct Hv as [OPT Hv]. 
        destruct Hv as [Hvu HvQ]. destruct HvQ as [HvQ Hv]. rewrite Hv.
        match goal with |[ |- context[_ (Match (?x::B0) A0)]] => set(a1:=x) end.
        assert(HM0:exists M0, (Is_uniform M0 (a1::B0) A0)/\
        (Vol(OPT) = Vol(M0) + oquantity a)). destruct Hvu as [Hopt1 Hopt2].
        apply remove_ab_transactions_main in Hopt2. destruct Hopt2 as [M0 Hopt2].
        rewrite reduced_equation_1 in Hopt2. rewrite reduced_equation_1 in Hopt2. 
        destruct (Compare_dec.le_lt_dec (oquantity b) (oquantity a)) eqn:Hba;
        destruct (Compare_dec.le_lt_dec (oquantity a) (oquantity b)) eqn:Hab.
        { lia. } { lia. } { exists M0. split. subst a1. replace (MatchingAlter.reduced_obligations_obligation_1 a b l0) with (Match.Match_obligations_obligation_1 b a l) in Hopt2. apply Hopt2. admit.
 destruct Hopt2. rewrite H8. lia. } {lia. } apply Hopt1. auto. destruct HM0 as [M0 HMv]. 
        destruct HMv as [HMu HMQ]. rewrite HMQ. cut(Vol M0 <= Vol (Match (a1 :: B0) A0)).
        lia. subst a1. apply H. all:simpl;auto. eauto. apply SortedreducedB with (b:=b).
        all:simpl;auto. apply Sorted_inv in H6. apply H6. split. auto. auto. 
        move /eqP in price. lia.
      }
    }
    { simpl. destruct (Nat.leb (Vol(M)) (min (oquantity b) (oquantity a))) eqn:Hqab.
      { move /leP in Hqab. 
        replace (Nat.min (oquantity b) (oquantity a)) with (oquantity a) in Hqab. 
        lia. lia. }
      { move /leP in Hqab. assert(Hv:Vol M >= Nat.min (oquantity b) (oquantity a)). lia.
        apply (exists_opt B0 A0 _ _ _) in Hv. all:auto. destruct Hv as [OPT Hv]. 
        destruct Hv as [Hvu HvQ]. destruct HvQ as [HvQ Hv]. rewrite Hv.
        assert(HM0:exists M0, (Is_uniform M0 B0 A0)/\
        (Vol(OPT) = Vol(M0) + oquantity a)). destruct Hvu as [Hopt1 Hopt2].
        apply remove_ab_transactions_main in Hopt2. destruct Hopt2 as [M0 Hopt2].
        rewrite reduced_equation_1 in Hopt2. rewrite reduced_equation_1 in Hopt2. 
        destruct (Compare_dec.le_lt_dec (oquantity b) (oquantity a)) eqn:Hba;
        destruct (Compare_dec.le_lt_dec (oquantity a) (oquantity b)) eqn:Hab.
        { exists M0. split. apply Hopt2. destruct Hopt2. rewrite H8. lia. } {lia. } { lia. } { lia. } 
        apply Hopt1. auto. destruct HM0 as [M0 HMv]. 
        destruct HMv as [HMu HMQ]. rewrite HMQ. cut(Vol M0 <= Vol (Match B0 A0)).
        lia. apply H0. all:simpl;auto. eauto. eauto. apply Sorted_inv in H5. apply H5.
        apply Sorted_inv in H6. apply H6. split. auto. auto. 
        move /eqP in price. lia.
      }
    }
  }
  { simpl. destruct (Nat.leb (Vol(M)) (min (oquantity b) (oquantity a))) eqn:Hqab.
      { move /leP in Hqab. 
        replace (Nat.min (oquantity b) (oquantity a)) with (oquantity b) in Hqab. 
        lia. lia. }
      { move /leP in Hqab. assert(Hv:Vol M >= Nat.min (oquantity b) (oquantity a)). lia.
        apply (exists_opt B0 A0 _ _ _) in Hv. all:auto. destruct Hv as [OPT Hv]. 
        destruct Hv as [Hvu HvQ]. destruct HvQ as [HvQ Hv]. rewrite Hv.
        match goal with |[ |- context[_ (Match B0 (?x::A0))]] => set(a1:=x) end.  
        assert(HM0:exists M0, (Is_uniform M0 B0 (a1::A0))/\
        (Vol(OPT) = Vol(M0) + oquantity b)). destruct Hvu as [Hopt1 Hopt2].
        apply remove_ab_transactions_main in Hopt2. destruct Hopt2 as [M0 Hopt2].
        rewrite reduced_equation_1 in Hopt2. rewrite reduced_equation_1 in Hopt2. 
        destruct (Compare_dec.le_lt_dec (oquantity b) (oquantity a)) eqn:Hba;
        destruct (Compare_dec.le_lt_dec (oquantity a) (oquantity b)) eqn:Hab.
        { lia. } { exists M0. split. subst a1. replace (MatchingAlter.reduced_obligations_obligation_1 b a l1) with (Match.Match_obligations_obligation_4 b a l) in Hopt2. apply Hopt2. admit.
 destruct Hopt2. rewrite H8. lia. } {lia. } { lia. } apply Hopt1. auto. destruct HM0 as [M0 HMv]. 
        destruct HMv as [HMu HMQ]. rewrite HMQ. cut(Vol M0 <= Vol (Match B0 (a1 :: A0))).
        lia. subst a1. apply H1. all:simpl;auto. eauto. apply Sorted_inv in H5. apply H5.
        apply SortedreducedA with (a:=a). all:simpl;auto. split. auto. auto. 
        move /eqP in price. lia.
      }
    }
  } assert(HaS2: forall x, In x A0 -> (Nat.leb (oprice a) (oprice x))). 
    apply Sorted_ointroA. auto. 
    assert(HbS2: forall x, In x B0 -> (Nat.leb (oprice x) (oprice b))).
    apply Sorted_ointroB. auto. 
    assert(~matchable (b :: B0) (a::A0)). 
    + intro. unfold matchable in H7. 
        destruct H7 as [b0 H9]. destruct H9 as [a0' H9]. destruct H9. 
        destruct H8. simpl in H7. simpl in H8. destruct H7;destruct H8.
        -- subst b0;subst a0'. unfold tradable in H9. move /eqP in price. lia.
        -- subst a0'. apply HbS2 in H8. unfold tradable in H9. move /eqP in price. 
           move /leP in H8. lia.
        -- subst b0. apply HaS2 in H7. unfold tradable in H9. move /eqP in price. 
           move /leP in H7. lia.
        -- apply HaS2 in H7. apply HbS2 in H8. unfold tradable in H9. 
           move /eqP in price. move /leP in H7. move /leP in H8. lia.
    + apply not_matchable_matching_nil with (M:=M) in H7. rewrite H7. simpl. lia. auto.
Admitted.


End UM.