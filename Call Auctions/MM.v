Require Export mUM.

Section MM.


Definition MM B A:=
(Match (Decr_Bid.sort B) (Decr_Ask.sort A)).


(*Definition MM_matching (B:list order) (A:list order) : (list transaction) :=
  FOA (UM B A) A. *)

Theorem MM_Is_Matching (B:list order)(A:list order)
(NDB: NoDup (ids B))(NDA: NoDup (ids A)):
Matching (MM B A) B A.
Proof. unfold MM. Admitted.

(*Move this lemma into another file*)
Lemma exists_ttq_top_bid 
(B:list order)(A:list order)(M:list transaction)(b:order)
(NDA:NoDup (ids A))(NDB:NoDup (ids (b::B))):
Sorted bcompetitive (b::B) -> 
 (Matching M (b::B) A) -> 
(exists M', (Matching M' (b::B) A)/\
(Qty_bid M' (id b) >= min (oquantity b) (Vol(M)))/\
Vol(M) = Vol(M')).
Proof. Admitted.

Lemma MM_exists_opt_k (B A:list order)(b a: order)
(NDA:NoDup (ids (a::A)))(NDB:NoDup (ids (b::B))):
Sorted bcompetitive (b::B) -> 
Sorted rev_acompetitive (a::A) -> 
(forall k M, Matching M (b::B) (a::A) ->
oprice b >= oprice a ->
Vol(M) >= (min (oquantity b) (oquantity a)) ->
(*(Qty_bid M (id b) >= (min (oquantity b) (oquantity a))) ->*)
(min (oquantity b) (oquantity a)) - Qty M (id b) (id a) = k ->
(exists M0, (Matching M0 (b::B) (a::A))/\Vol(M)=Vol(M0)/\
(min (oquantity b) (oquantity a)) - Qty M0 (id b) (id a) = 0)).
Proof. revert B A b a NDA NDB. induction k. 
       { intros M Match price_ab HvM HQab. exists M. split;auto. }
       { intros M Match price_ab HvM k_n.    (*Main induction case*)
          case (Nat.leb (oquantity b) (oquantity a)) eqn:Hab.
          { assert ((min (oquantity b) (oquantity a)) = oquantity b). 
            eapply min_l. move /leP in Hab;lia.
            assert(Qty M (id b) (id a) < (oquantity b)). lia.
            rewrite H1 in k_n.
            rewrite H1. assert(Qbid:((Qty_bid M (id b)) < (oquantity b))\/((Qty_bid M (id b)) >= (oquantity b))).
            lia. destruct Qbid as [Qbid | Qbid].
            assert(Htmp:Qty M (id b) (id a) < Qty_bid M (id b)\/Qty M (id b) (id a) >= Qty_bid M (id b)). lia.
            destruct Htmp as [H3 | H3]. 
            assert(Qask:((Qty_ask M (id a)) > (oquantity a))\/((Qty_ask M (id a)) = (oquantity a))\/
            ((Qty_ask M (id a)) < (oquantity a))). lia. destruct Qask as [Qask | Qask].
            assert(((Qty_ask M (id a)) <= (oquantity a))). apply Match. all:auto. lia.
            destruct Qask as [Qask | Qask].
            { (* Case when a is fully traded in M *)
              apply Qty_lt_Qty_bid_m_exists in H3.  assert(Qty M (id b) (id a) < Qty_ask M (id a)). lia.
              apply Qty_lt_Qty_ask_m_exists in H4. destruct H3 as [m1 H3]. destruct H4 as [m2 H4]. destruct H3.
              destruct H5. destruct H4. destruct H7. 
              apply increase_ab_quantity_Matching with (m1:=m1)(m2:=m2)(b:=b)(a:=a) in Match.
              apply IHk in Match. destruct Match as [M0 Match].          
              exists M0. split. apply Match. split. rewrite (increase_ab_quantity_Vol _ m1 m2 b a). all:auto.
              intro. subst m1. lia. apply Match. rewrite <- H1. apply Match.  
              rewrite <- (increase_ab_quantity_Vol _ m1 m2 b a). all:auto.
              intro. subst m1. lia.  rewrite (increase_ab_quantity_extra _ m1 m2 b a). all:auto. intro;subst m1;lia.
              lia. intro;subst m1;lia.
             }
             { apply Qty_lt_Qty_bid_m_exists in H3. destruct H3 as [m H3]. destruct H3.
               destruct H4. apply increase_b_quantity_Matching with (m:=m)(b:=b)(a:=a) in Match.
               apply IHk in Match. destruct Match as [M0 Match]. exists M0. split. apply Match. split.
               rewrite (increase_b_quantity_Vol _ m b a). all:auto. apply Match. rewrite <- H1. apply Match.  
               rewrite <- (increase_b_quantity_Vol _ m b a). all:auto. rewrite H1. 
               rewrite (increase_b_quantity_extra _ m b a).
               all:auto. lia.
             } 

          }


Lemma MM_exists_opt_k (B A:list order)(b a: order)
(NDA:NoDup (ids (a::A)))(NDB:NoDup (ids (b::B))):
Sorted bcompetitive (b::B) -> 
Sorted rev_acompetitive (a::A) -> 
(forall k M, Matching M (b::B) (a::A) ->
oprice b >= oprice a ->
Vol(M) >= (min (oquantity b) (oquantity a)) ->
(Qty_bid M (id b) >= (min (oquantity b) (oquantity a))) ->
(min (oquantity b) (oquantity a)) - Qty M (id b) (id a) = k ->
(exists M0, (Matching M0 (b::B) (a::A))/\Vol(M)=Vol(M0)/\
(min (oquantity b) (oquantity a)) - Qty M0 (id b) (id a) = 0)).
Proof. revert B A b a NDA NDB. induction k. 
       { intros M Match price_ab HvM HQb HQab. exists M. split;auto. }
       { intros M Match price_ab HvM HQb k_n.    (*Main induction case*)
          case (Nat.leb (oquantity b) (oquantity a)) eqn:Hab.
          { assert ((min (oquantity b) (oquantity a)) = oquantity b). 
            eapply min_l. move /leP in Hab;lia.
            assert(Qty M (id b) (id a) < (oquantity b)). lia.
            rewrite H1 in k_n.
            rewrite H1. assert(Qbid:((Qty_bid M (id b)) < (oquantity b))\/((Qty_bid M (id b)) >= (oquantity b))).
            lia. destruct Qbid as [Qbid | Qbid].
            assert(((Qty_bid M (id b)) <= (oquantity b))). apply Match. all:auto. lia.
            assert(Qty M (id b) (id a) < Qty_bid M (id b)). lia.
            assert(Qask:((Qty_ask M (id a)) > (oquantity a))\/((Qty_ask M (id a)) = (oquantity a))\/
            ((Qty_ask M (id a)) < (oquantity a))). lia. destruct Qask as [Qask | Qask].
            assert(((Qty_ask M (id a)) <= (oquantity a))). apply Match. all:auto. lia.
            destruct Qask as [Qask | Qask].
            { (* Case when a is fully traded in M *)
              apply Qty_lt_Qty_bid_m_exists in H3.  assert(Qty M (id b) (id a) < Qty_ask M (id a)). lia.
              apply Qty_lt_Qty_ask_m_exists in H4. destruct H3 as [m1 H3]. destruct H4 as [m2 H4]. destruct H3.
              destruct H5. destruct H4. destruct H7. 
              apply increase_ab_quantity_Matching with (m1:=m1)(m2:=m2)(b:=b)(a:=a) in Match.
              apply IHk in Match. destruct Match as [M0 Match].          
              exists M0. split. apply Match. split. rewrite (increase_ab_quantity_Vol _ m1 m2 b a). all:auto.
              intro. subst m1. lia. apply Match. rewrite <- H1. apply Match.  
              rewrite <- (increase_ab_quantity_Vol _ m1 m2 b a). all:auto.
              intro. subst m1. lia. rewrite H1. rewrite increase_ab_quantity_Qty_bid. all:auto. 
              intro;subst m1;lia. rewrite (increase_ab_quantity_extra _ m1 m2 b a). all:auto. intro;subst m1;lia.
              lia. intro;subst m1;lia.
             }
             { apply Qty_lt_Qty_bid_m_exists in H3. destruct H3 as [m H3]. destruct H3.
               destruct H4. apply increase_b_quantity_Matching with (m:=m)(b:=b)(a:=a) in Match.
               apply IHk in Match. destruct Match as [M0 Match]. exists M0. split. apply Match. split.
               rewrite (increase_b_quantity_Vol _ m b a). all:auto. apply Match. rewrite <- H1. apply Match.  
               rewrite <- (increase_b_quantity_Vol _ m b a). all:auto. rewrite H1. 
               rewrite increase_b_quantity_Qty_bid. all:auto. rewrite (increase_b_quantity_extra _ m b a).
               all:auto. lia.
             }
          }
          { assert ((min (oquantity b) (oquantity a)) = oquantity a). 
            eapply min_r. move /leP in Hab;lia.
            assert(Qty M (id b) (id a) < (oquantity a)). lia.
            rewrite H1 in k_n. rewrite H1 in HQb.  rewrite H1.
            assert(Qty M (id b) (id a) < Qty_bid M (id b)). lia.
            assert(Qask:((Qty_ask M (id a)) > (oquantity a))\/((Qty_ask M (id a)) = (oquantity a))\/
            ((Qty_ask M (id a)) < (oquantity a))). lia. destruct Qask as [Qask | Qask].
            assert(((Qty_ask M (id a)) <= (oquantity a))). apply Match. all:auto. lia.
            destruct Qask as [Qask | Qask].
            { (* Case when a is fully traded in M *)
              apply Qty_lt_Qty_bid_m_exists in H3.  assert(Qty M (id b) (id a) < Qty_ask M (id a)). lia.
              apply Qty_lt_Qty_ask_m_exists in H4. destruct H3 as [m1 H3]. destruct H4 as [m2 H4]. destruct H3.
              destruct H5. destruct H4. destruct H7. 
              apply increase_ab_quantity_Matching with (m1:=m1)(m2:=m2)(b:=b)(a:=a) in Match.
              apply IHk in Match. destruct Match as [M0 Match].          
              exists M0. split. apply Match. split. rewrite (increase_ab_quantity_Vol _ m1 m2 b a). all:auto.
              intro. subst m1. lia. apply Match. rewrite <- H1. apply Match.  
              rewrite <- (increase_ab_quantity_Vol _ m1 m2 b a). all:auto.
              intro. subst m1. lia. rewrite H1. rewrite increase_ab_quantity_Qty_bid. all:auto. 
              intro;subst m1;lia. rewrite (increase_ab_quantity_extra _ m1 m2 b a). all:auto. intro;subst m1;lia.
              lia. intro;subst m1;lia.
             }
             { apply Qty_lt_Qty_bid_m_exists in H3. destruct H3 as [m H3]. destruct H3.
               destruct H4. apply increase_b_quantity_Matching with (m:=m)(b:=b)(a:=a) in Match.
               apply IHk in Match. destruct Match as [M0 Match]. exists M0. split. apply Match. split.
               rewrite (increase_b_quantity_Vol _ m b a). all:auto. apply Match. rewrite <- H1. apply Match.  
               rewrite <- (increase_b_quantity_Vol _ m b a). all:auto. rewrite H1. 
               rewrite increase_b_quantity_Qty_bid. all:auto. rewrite (increase_b_quantity_extra _ m b a).
               all:auto. lia.
             }
} } Qed.



Lemma MM_exists_opt (B:list order)(A:list order)(M:list transaction)(b:order)(a:order)
(NDA:NoDup (ids (a::A)))(NDB:NoDup (ids (b::B))):
Sorted bcompetitive (b::B) -> 
Sorted rev_acompetitive (a::A) -> 
(Matching M (b::B) (a::A)) -> 
oprice b >= oprice a ->
Vol(M) >= (min (oquantity b) (oquantity a)) ->
(exists M', (Matching M' (b::B) (a::A))/\
(min (oquantity b) (oquantity a)) = Qty M (id b) (id a)/\Vol(M)=Vol(M')).
Proof. Proof. intros. destruct ((min (oquantity b) (oquantity a)) - Qty M (id b) (id a)) eqn:Hk.
exists M. split. auto. split. admit. auto. 
apply MM_exists_opt_k with (M:=M)(A:=A)(B:=B)(k:=S n)(b:=b)(a:=a) in H1.
destruct H1 as [M0 H1]. destruct H1. destruct H4. exists M0. split. auto.
split. admit. all:auto. admit. split. admit. auto. Admitted. (*Use Qty_le_Qty_bid to clear admits *)


Admitted.
(*
Proof. intros. 
       assert(exists M', (matching_in (b::B) (a::A) M')/\
       (ttqb M' b >= min (bq b) (QM(M)))/\Is_IR M'/\QM(M)=QM(M')/\
       forall m : fill_type, In m M' -> tq m > 0).
       eapply exists_ttq_top_bid. all:auto. 
       destruct H5 as [M0 H5].
       destruct H5. destruct H6. destruct H7. 
       destruct (Nat.min (bq b) (sq a) - ttq_ab M0 b a) eqn:Hk.
       {
         eapply MM_exists_opt_k with (k:=0)(A:=A)(a:=a)(B:=B)(b:=b) in H5.
         destruct H5 as [OPT H5]. exists OPT. 
         destruct H5. destruct H9.
         split. apply H5. split. 
         assert (Hmin:ttq_ab OPT b a <= Nat.min (bq b) (sq a)).
         eapply matching_in_elim9 with (B:=(b::B))(A:=(a::A)).
         apply H5. auto.
         split. assert (Hmin:ttq_ab OPT b a <= Nat.min (bq b) (sq a)).
         eapply matching_in_elim9 with (B:=(b::B))(A:=(a::A)).
         all:auto. lia. split. destruct H10. destruct H8. lia.
         apply H10. lia. lia.  apply H8.
       }  
       { assert(Haba:ttqa M0 a >=ttq_ab M0 b a).
         eauto. 
         eapply MM_exists_opt_k with (k:= S n)(A:=A)(a:=a)(B:=B)(b:=b) in H5.
         destruct H5 as [OPT H5]. exists OPT. 
         destruct H5. destruct H9.
         split. apply H5. split. 
         assert (Hmin:ttq_ab OPT b a <= Nat.min (bq b) (sq a)).
         eapply matching_in_elim9 with (B:=(b::B))(A:=(a::A)).
         apply H5. auto.
         split. assert (Hmin:ttq_ab OPT b a <= Nat.min (bq b) (sq a)).
         eapply matching_in_elim9 with (B:=(b::B))(A:=(a::A)).
         all:auto. lia. split. destruct H10. destruct H8. lia.
         apply H10. lia. lia.  apply H8.
       }
Qed. 


Lemma matching_in_elim10 (B:list order)(A:list order)(M:list transaction)(a:order)(b:order)
(NDA:NoDup (a::A))(NDB:NoDup (b::B)):
Sorted by_dsp (a::A) ->
Sorted by_dbp (b::B) ->
b<a ->
matching_in (b::B) (a::A) M ->
~In a (asks_of M).
Proof. intros. induction M as [|m M'].
simpl. eauto.
assert(ask_of m <= bid_of m).
apply H2. auto.
assert(In (ask_of m) (a::A)).
apply H2. simpl. auto.
assert(In (bid_of m) (b::B)).
apply H2. simpl. auto.
destruct H4;destruct H5.
{
subst. lia.
}
{
eapply Sorted_elim2 with (x:=(bid_of m)) in H0.
unfold by_dbp in H0. move /orP in H0.
destruct H0. move /leP in H0. subst. lia.
move /andP in H0. destruct H0. move /eqP in H0.
subst. lia. apply by_dbp_refl. eauto.
}
{
simpl.
intro. destruct H6. subst. lia.
assert(exists m', In m' M'/\a = ask_of m'). eauto.
destruct H7 as [m0 H7]. destruct H7. 
assert(ask_of m0 <= bid_of m0).
apply H2. auto.
eapply Sorted_elim2 with (x:=(bid_of m0)) in H0.
unfold by_dbp in H0. move /orP in H0.
destruct H0. move /leP in H0. subst. lia.
move /andP in H0. destruct H0. move /eqP in H0.
subst. lia. apply by_dbp_refl. apply H2.
simpl. right. eauto.
}
{
intro. simpl in H6. destruct H6.
rewrite H6 in H4. assert(~In a A).
eauto. eauto.
assert(exists m', In m' M'/\a = ask_of m'). eauto.
destruct H7 as [m0 H7]. destruct H7. 
assert(ask_of m0 <= bid_of m0).
apply H2. auto.
eapply Sorted_elim2 with (x:=(bid_of m0)) in H0.
unfold by_dbp in H0. move /orP in H0.
destruct H0. move /leP in H0. subst. lia.
move /andP in H0. destruct H0. move /eqP in H0.
subst. lia. apply by_dbp_refl. apply H2.
simpl. right. eauto.
}
Qed.


Lemma matching_in_elim11 (B:list order)(A:list order)(M:list transaction)(a:order)(b:order)
(NDA:NoDup (a::A))(NDB:NoDup (b::B)):
Sorted by_dsp (a::A) ->
Sorted by_dbp (b::B) ->
b<a ->
matching_in (b::B) (a::A) M ->
matching_in (b::B) A M.
Proof. intros. assert(~In a (asks_of M)).
eapply matching_in_elim10 in H2. all:auto.
split. split. apply H2.
split. apply H2. apply H2.
split. apply H2. assert(asks_of M [<=] a::A).
apply H2. eauto. Qed.

*)

(*
Theorem MM_aux_OPT (B:list order)(A:list order)(M:list transaction)
(b:order)(a:order)(ta tb: nat)
(NDA:NoDup (ida a::(idas_of A)))(NDB:NoDup (idb b::(idbs_of B)))
(NZT: forall m : fill_type, In m M -> tq m > 0)
(NZB: forall b0, In b0 ((Mk_bid (bp b) (btime b) (bq b - tb) (idb b))::B) -> (bq b0)>0)
(NZA: forall a0, In a0 ((Mk_ask (sp a) (stime a) (sq a - ta) (ida a))::A) -> (sq a0)>0):
Sorted by_dbp (b::B) -> 
Sorted by_dsp (a::A) -> 
matching_in ((Mk_bid (bp b) (btime b) (bq b - tb) (idb b))::B)
                        ((Mk_ask (sp a) (stime a) (sq a - ta) (ida a))::A) M ->
Is_IR M -> 
QM(M) <= QM(MM_aux (b::B) (a::A) tb ta).
Proof. intros. 
assert(HBS: Sorted by_dbp ((Mk_bid (bp b) (btime b) (bq b - tb) (idb b))::B)).
constructor. eauto. intros. 
eapply Sorted_elim4 with (x0:=x) in H.
destruct b;destruct x. auto. auto.
assert(HAS: Sorted by_dsp ((Mk_ask (sp a) (stime a) (sq a - ta) (ida a))::A)).
constructor. eauto. intros. 
eapply Sorted_elim4 with (x0:=x) in H0.
destruct a;destruct x. auto. auto.
funelim (MM_aux (b::B) (a::A) tb ta).
rewrite <- Heqcall. 
destruct (Nat.leb a b) eqn: Hab.
{ 
  assert(Hab0: a <= b). move /leP in Hab. auto.
  destruct (Nat.leb (QM(M)) (min (bq b - tb) (sq a - ta))) eqn:Hqab.
  { 
    move /leP in Hqab.
    destruct (Nat.eqb (bq b - tb) (sq a - ta)). simpl. lia.
    destruct (Nat.leb (bq b - tb) (sq a - ta)) eqn:Hle.
    simpl. lia. simpl.
    move /eqP in Hle. lia.
  }
  {
    eapply MM_exists_opt in H5.
    all:auto. 
    destruct H5 as [M0 H5].
    destruct H5. destruct H7. destruct H8. destruct H9. rewrite H9.
    destruct (Nat.eqb (bq b - tb) (sq a - ta)) eqn: Hqabeq.
    {
      simpl. simpl in H8.
      assert(HM0':exists M0', 
      (matching_in l l0 M0')/\Is_IR M0'/\(QM(M0)=QM(M0') + (bq b - tb))/\
      (forall m : fill_type, In m M0' -> tq m > 0)).
      {
        eapply exists_M0_reduced_bid_ask_matching in H5.
        simpl in H5.
        destruct H5 as [M1 H5]. exists M1. split. apply H5.
        split. apply H5. split. apply H5. apply H5.
        auto. simpl.
        move /eqP in Hqabeq. lia.
        auto.
      }
      destruct HM0' as [M0' HM0'].
      replace (QM M0) with (QM M0' + (bq b - tb)).
      cut(QM M0' <= QM (MM_aux l l0 0 0)). lia.
      case l eqn: Hl. simp MM_aux.
      simpl.
      { simp UM_aux.
        simpl.  
        { destruct HM0'. 
          apply matching_on_nilB in H11. 
          rewrite H11.  simpl. lia. }
      }
      case l0 eqn: Hl0. simp MM_aux.
        { simp UM_aux.
          simpl. destruct HM0'. 
          apply matching_on_nilA in H11. 
          rewrite H11.  simpl. lia.
        }
      eapply H with (M:=M0'). all:auto.
      eauto. eauto. apply HM0'. 
      { intros.
        destruct H11. subst b1. simpl. 
        replace (bq b0 - 0) with (bq b0). eauto.
        lia. eauto. 
      }
      { intros.
            destruct H11. subst a1. simpl. 
            replace (sq a0 - 0) with (sq a0). eauto.
            lia. eauto. 
      } 
      eauto. 
      eauto.
      { replace (bq b0 - 0) with (bq b0).
        replace (sq a0 - 0) with (sq a0).
        destruct HM0'. destruct b0;destruct a0. intros. 
        eapply H11.  lia. lia.
      }  
      apply HM0'.
      { replace (bq b0 - 0) with (bq b0).
            assert(Sorted by_dbp (b0 :: l1));eauto;destruct b0;auto.
            lia.
      }
      { replace (sq a0 - 0) with (sq a0). 
        assert(Sorted by_dsp (a0 :: l2));eauto;destruct a0;auto.
        lia. 
      }
     destruct HM0'. destruct H12. destruct H13;auto.
    }
    {
      destruct (Nat.leb (bq b - tb) (sq a - ta)) eqn:Hle.
      {
        simpl. simpl in H6.
        case l eqn: Hl. simp MM_aux. simpl.
        { simp UM_aux.
          simpl. 
          apply matching_on_bnill in H5.
          simpl in H5. lia.
        } 
        assert(HM0':exists M0', (matching_in 
        ((Mk_bid (bp b0) (btime b0) (bq b0 - 0) (idb b0))::l1) 
        ((Mk_ask (sp a) (stime a) (sq a - (ta + (bq b - tb))) (ida a))::l0)
         M0')
        /\Is_IR M0'/\(QM(M0)=QM(M0') + (bq b - tb))/\
          (forall m : fill_type, In m M0' -> tq m > 0)).
        {
         eapply exists_M0_reduced_ask_matching with (b:=
         {|
          bp := b;
          btime := btime b;
          bq := bq b - tb;
          idb := idb b |}) in H5.
         destruct H5 as [M1 H5]. exists M1.
         all:auto. simpl in H5. 
         replace (sq a - (ta + (bq b - tb))) with (sq a - ta - (bq b - tb)).
         replace (bq b0 - 0) with (bq b0). 
         replace ({| bp := b0; btime := btime b0; bq := bq b0; idb := idb b0 |})
         with b0. split. eapply H5. split. apply H5.
         split. apply H5. apply H5.
         destruct b0. simpl. auto.
         lia. lia. simpl in H8. simpl. auto.
         move /leP in Hle. lia. 
         move /eqP in Hqabeq. move /leP in Hle. 
         simpl. lia.
        } 
        destruct HM0' as [M0' HM0'].
        replace (QM M0) with (QM M0' + (bq b - tb)).
        cut(QM M0' <= QM (MM_aux (b0 :: l1) (a :: l0) 0 (ta + (bq b - tb)))).
        lia.
        eapply H0 with (M:=M0'). all:auto.
        eauto. all: try apply HM0'. 
        { move /leP in Hle. intros.
            destruct H11. subst b1. simpl.
            replace (bq b0 - 0) with (bq b0). eauto.
            lia. eauto.
        }
        { move /leP in Hle. intros.
          destruct H11. subst a0. simpl. move /eqP in Hqabeq. lia. eauto. 
        }
        eauto.
        { replace (bq b0 - 0) with (bq b0). destruct b0;auto. eauto. 
            lia.
        } 
        {
        constructor. eauto. intros. simpl.          
        eapply Sorted_elim4 with (x0:=x) in H4.
        destruct a;destruct x. unfold by_dsp. simpl.
        unfold by_dsp in H4. simpl in H4. auto. auto.
        }
        destruct HM0'. destruct H12. destruct H13. lia. 
      }
      {
        simpl. simpl in H6.
        case l0 eqn: Hl0. simp MM_aux. simpl.
        { simp UM_aux.
          simpl. simpl in H5. 
          apply matching_on_anill in H5.
          simpl in H5. simpl. lia.
        } 
        assert(HM0':exists M0', (matching_in 
       ((Mk_bid (bp b) (btime b) (bq b - (tb + (sq a - ta))) (idb b))::l)
       ((Mk_ask (sp a0) (stime a0) (sq a0 - 0) (ida a0))::l1)
       M0')
       /\Is_IR M0'/\(QM(M0)=QM(M0') + (sq a - ta))/\
       (forall m : fill_type, In m M0' -> tq m > 0)).
        {
         eapply exists_M0_reduced_bid_matching with (a:=
         {|
          sp := a;
          stime := stime a;
          sq := sq a - ta;
          ida := ida a |}) in H5. all:auto.
         destruct H5 as [M1 H5]. exists M1.
         destruct H5. simpl in H5. 
         replace (bq b - (tb + (sq a - ta))) with (bq b - tb - (sq a - ta)).
         split. replace (sq a0 - 0) with (sq a0).
         replace ({| sp := a0; stime := stime a0; sq := sq a0; ida := ida a0 |})
         with a0. eapply H5. destruct a0. simpl. auto.
         lia. simpl in H11. split. apply H11. split. apply H11.
         apply H11. lia.
         simpl.
         move /leP in Hle. simpl in H8.  lia. 
         move /eqP in Hqabeq. move /leP in Hle. 
         simpl. lia.
        }
        destruct HM0' as [M0' HM0'].
        replace (QM M0) with (QM M0' + (sq a - ta)).
        cut(QM M0' <= QM (MM_aux (b :: l) (a0 :: l1) (tb + (sq a - ta)) 0)).
        lia.
        eapply H1 with (M:=M0'). all:auto.
        eauto. all: try apply HM0'. 
        { move /leP in Hle. intros.
            destruct H11. subst b0. simpl.
             move /eqP in Hqabeq. lia. eauto.
        }
        { move /leP in Hle. intros.
          destruct H11. subst a1. simpl. 
        replace (sq a0 - 0) with (sq a0). eauto. 
        lia. eauto.
        }
        eauto.
        { constructor. eauto. intros. simpl. 
          eapply Sorted_elim4 with (x0:=x) in H3.
          destruct b;destruct x. unfold by_dsp. simpl.
          unfold by_dsp in H3. simpl in H3. auto. auto.
        }
        { replace (sq a0 - 0) with (sq a0). destruct a0;auto. eauto. 
            lia.
        } 
        destruct HM0'. destruct H12. destruct H13. lia. 
        }
      }
      simpl. move /leP in Hqab. lia. 
    }
  }
  {
  case l0 eqn: Hl0. 
  assert(Hbla:b<a).
  move /leP in Hab. lia.
  apply matching_in_elim11 in H5.
  apply matching_on_nilA in H5. 
  rewrite H5. simpl. lia. eauto. eauto.
  eauto. eauto. auto. apply H2. all:auto. eauto.
  intros. destruct H7. subst a1. simpl. 
  replace (sq a0 - 0) with (sq a0). eauto. lia. eauto.
  eauto. apply matching_in_elim11 in H5. 
  replace (sq a0 - 0) with (sq a0). 
  destruct a0. apply H5. lia. eauto. eauto.
  eauto. eauto. auto. simpl. move /leP in Hab. lia. 
  replace (sq a0 - 0) with (sq a0). destruct a0;auto. eauto. 
  lia.
} 
Qed. *)


Theorem MM_aux_optimal (B:list order)(A:list order)(M:list transaction):
(NoDup (ids A)) -> (NoDup (ids B)) ->
Sorted bcompetitive B -> 
Sorted rev_acompetitive A -> 
(Matching M B A) -> 
Vol(M) <= Vol(Match B A).
Proof. revert M. apply Match_elim. 
- firstorder. unfold Tvalid in H3. unfold valid in H3. induction M as [|t M]. simpl.
auto. assert(In t (t::M)). simpl;auto. apply H3 in H6. destruct H6. destruct H6.
firstorder.
- firstorder. unfold Tvalid in H3. unfold valid in H3. induction M as [|t M]. simpl.
auto. assert(In t (t::M)). simpl;auto. apply H3 in H6. firstorder.
- intros.
assert(HaS: forall x, In x A0 -> (acompetitive x a)). apply Sorted_ointro_not_A_tight. auto.
assert(HbS: forall x, In x B0 -> (bcompetitive b x)). apply Sorted_ointroB_tight. auto.
destruct (PeanoNat.Nat.eqb (oprice a - oprice b) 0) eqn:price.
{ destruct (Compare_dec.lt_eq_lt_dec (oquantity a) (oquantity b)) eqn:f1. 
  { destruct s eqn:f2.
    { specialize (H s). specialize (H l). simpl. 
      destruct (Nat.leb (Vol(M)) (min (oquantity b) (oquantity a))) eqn:Hqab.
      { move /leP in Hqab. 
        replace (Nat.min (oquantity b) (oquantity a)) with (oquantity a) in Hqab. 
        lia. lia. }
      { move /leP in Hqab. assert(Hv:Vol M >= Nat.min (oquantity b) (oquantity a)). lia.
        apply (MM_exists_opt B0 A0 _ _ _) in Hv. all:auto. destruct Hv as [OPT Hv]. 
        destruct Hv as [Hvu HvQ]. destruct HvQ as [HvQ Hv]. rewrite Hv.
        match goal with |[ |- context[_ (Match (?x::B0) A0)]] => set(a1:=x) end.  
        assert(HM0:exists M0, (Matching M0 (a1::B0) A0)/\
        (Vol(OPT) = Vol(M0) + oquantity a)). admit. destruct HM0 as [M0 HMv]. 
        destruct HMv as [HMu HMQ]. rewrite HMQ. cut(Vol M0 <= Vol (Match (a1 :: B0) A0)).
        lia. subst a1. apply H. all:simpl;auto. eauto. apply SortedreducedB with (b:=b).
        all:simpl;auto. apply Sorted_inv in H6. apply H6. 
        move /eqP in price. lia.
      }
    }
    { simpl. destruct (Nat.leb (Vol(M)) (min (oquantity b) (oquantity a))) eqn:Hqab.
      { move /leP in Hqab. 
        replace (Nat.min (oquantity b) (oquantity a)) with (oquantity a) in Hqab. 
        lia. lia. }
      { move /leP in Hqab. assert(Hv:Vol M >= Nat.min (oquantity b) (oquantity a)). lia.
        apply (MM_exists_opt B0 A0 _ _ _) in Hv. all:auto. destruct Hv as [OPT Hv]. 
        destruct Hv as [Hvu HvQ]. destruct HvQ as [HvQ Hv]. rewrite Hv.
        assert(HM0:exists M0, (Matching M0 B0 A0)/\
        (Vol(OPT) = Vol(M0) + oquantity a)). admit. destruct HM0 as [M0 HMv]. 
        destruct HMv as [HMu HMQ]. rewrite HMQ. cut(Vol M0 <= Vol (Match B0 A0)).
        lia. apply H0. all:simpl;auto. eauto. eauto. apply Sorted_inv in H5. apply H5.
        apply Sorted_inv in H6. apply H6.  auto. auto. 
        move /eqP in price. lia.
      }
    }
  }
  { simpl. destruct (Nat.leb (Vol(M)) (min (oquantity b) (oquantity a))) eqn:Hqab.
      { move /leP in Hqab. 
        replace (Nat.min (oquantity b) (oquantity a)) with (oquantity b) in Hqab. 
        lia. lia. }
      { move /leP in Hqab. assert(Hv:Vol M >= Nat.min (oquantity b) (oquantity a)). lia.
        apply (MM_exists_opt B0 A0 _ _ _) in Hv. all:auto. destruct Hv as [OPT Hv]. 
        destruct Hv as [Hvu HvQ]. destruct HvQ as [HvQ Hv]. rewrite Hv.
        match goal with |[ |- context[_ (Match B0 (?x::A0))]] => set(a1:=x) end.  
        assert(HM0:exists M0, (Matching M0 B0 (a1::A0))/\
        (Vol(OPT) = Vol(M0) + oquantity b)). admit. destruct HM0 as [M0 HMv]. 
        destruct HMv as [HMu HMQ]. rewrite HMQ. cut(Vol M0 <= Vol (Match B0 (a1 :: A0))).
        lia. subst a1. apply H1. all:simpl;auto. eauto. apply Sorted_inv in H5. apply H5.
        (* apply SortedreducedA with (a:=a). all:simpl;auto. *) admit. 
        move /eqP in price. lia.
      }
    }
  } apply H2. all:auto. eauto. apply Sorted_inv in H6. apply H6. admit.
Admitted.

End MM.