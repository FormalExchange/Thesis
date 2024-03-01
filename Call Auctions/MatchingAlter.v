Require Export Matching.
Require Export Match.
From Equations Require Export Equations.

Section Transform.

(*########UM Surgery for Q(b,a,M')  = Q(b,a,M) + 1 matching ############*)

(*This function g_increase_top takes two transactions ma and mb of M, where ask of ma is a and bid of mb is b. It reduces the trades quantity of ma and mb by 1 and inserts two transactions of single quantity between a <--> b and between partners if a and b. This is used in the proofs maximality for MM and UM. 
Here we proves correctness properties of g_increase_top.*)

Equations increase_ab_quantity (M:list transaction)(mb ma:transaction)(b:order)(a:order):(list transaction) :=  
increase_ab_quantity M mb ma b a := 
    (match ((Compare_dec.le_lt_dec (tquantity ma) 1), (Compare_dec.le_lt_dec (tquantity mb) 1)) with 
        |(left _ , left _ ) => ((Mk_transaction (id b) (id a) (tprice ma) 1 not1)::
                          (Mk_transaction (idb ma) (ida mb) (tprice ma) 1 not1)::
                          (delete mb (delete ma M))) 
        |(left _ , right _ ) => 
                   ((Mk_transaction (id b) (id a) (tprice ma) 1 not1)::
                    (Mk_transaction (idb ma) (ida mb) (tprice ma) 1 not1)::
                    (Mk_transaction (idb mb) (ida mb) (tprice mb) (tquantity mb - 1) _)::
                   (delete mb (delete ma M)))
        |(right _ , left _ ) => 
                ((Mk_transaction (id b) (id a) (tprice ma) 1 not1)::
                 (Mk_transaction (idb ma) (ida mb) (tprice ma) 1 not1)::
                 (Mk_transaction (idb ma) (ida ma) (tprice ma) (tquantity ma - 1) _ )::
                 (delete mb (delete ma M)))
       |(right _ , right _ ) =>
                ((Mk_transaction (id b) (id a) (tprice ma) 1 not1)::
                (Mk_transaction (idb ma) (ida mb) (tprice ma) 1 not1)::
                (Mk_transaction (idb ma) (ida ma) (tprice ma) (tquantity ma - 1) _)::
                (Mk_transaction (idb mb) (ida mb) (tprice mb) (tquantity mb - 1) _)::
                (delete mb (delete ma M))) end).

Next Obligation.
 apply PeanoNat.Nat.ltb_nlt. lia. Defined.  
Next Obligation.
 apply PeanoNat.Nat.ltb_nlt. lia. Defined.  
Next Obligation.
 apply PeanoNat.Nat.ltb_nlt. lia. Defined.  
Next Obligation.
 apply PeanoNat.Nat.ltb_nlt. lia. Defined.  

(*Proof that total Volume of matching has not changed due to above surgery *)
Lemma increase_ab_quantity_Vol (M:list transaction)(m1 m2:transaction)(b:order)(a:order):
In m1 M ->
In m2 M ->
m1<>m2 ->
Vol(M) = Vol(increase_ab_quantity M m1 m2 b a).
Proof. rewrite increase_ab_quantity_equation_1. intros. simpl.
       destruct (Compare_dec.le_lt_dec (tquantity m1) 1) eqn:Hm1;
       destruct (Compare_dec.le_lt_dec (tquantity m2) 1) eqn:Hm2.
       { simpl. assert (Hm2a: In m1 (delete m2 M)). apply delete_intro. auto. 
         intro.  destruct H1. auto. apply Vol_delete_m in Hm2a. apply Vol_delete_m in H0.
         assert(tquantity m2 = 1). destruct m2. simpl. simpl in l0.
         assert(Ht1:=tquantity_cond).  move /leP in Ht1. lia.
         assert(tquantity m1 = 1). destruct m1. simpl. simpl in l.
         assert(Ht1:=tquantity_cond).  move /leP in Ht1. lia. lia.
       }
       { simpl. assert (Hm2a: In m1 (delete m2 M)). apply delete_intro. auto. 
         intro.  destruct H1. auto. apply Vol_delete_m in Hm2a. apply Vol_delete_m in H0.
         assert(tquantity m1 = 1). destruct m1. simpl. simpl in l.
         assert(Ht1:=tquantity_cond).  move /leP in Ht1. lia. lia.
       }
       { simpl. assert (Hm2a: In m1 (delete m2 M)). apply delete_intro. auto. 
         intro.  destruct H1. auto. apply Vol_delete_m in Hm2a. apply Vol_delete_m in H0.
         assert(tquantity m2 = 1). destruct m2. simpl. simpl in l0.
         assert(Ht1:=tquantity_cond).  move /leP in Ht1. lia. lia. 
       }
       { simpl. assert (Hm2a: In m1 (delete m2 M)). apply delete_intro. auto. 
         intro.  destruct H1. auto. apply Vol_delete_m in Hm2a. apply Vol_delete_m in H0.
         lia.
       } Qed.

(*Proof that in increase_ab_quantity the trade quantity between a and b is increased by a single unit.*)
Lemma increase_ab_quantity_extra (M:list transaction)(m1 m2:transaction)(b:order)(a:order):
In m1 M ->
In m2 M ->
m1<>m2 ->
(id a) = (ida m2) ->
(id b) <> idb m2 ->
(id b) = (idb m1) ->
(id a) <> ida m1 ->
Qty (increase_ab_quantity M m1 m2 b a) (id b) (id a) = 1 + (Qty M (id b) (id a)).
Proof.
rewrite increase_ab_quantity_equation_1. intros.
       destruct (Compare_dec.le_lt_dec (tquantity m1) 1) eqn:Hm1;
       destruct (Compare_dec.le_lt_dec (tquantity m2) 1) eqn:Hm2.
       { simpl. replace (Nat.eqb (id b) (id b) && Nat.eqb (id a) (id a)) with true.
         replace (Nat.eqb (idb m2) (id b) && Nat.eqb (ida m1) (id a)) with false.
         assert (Hm2a: In m2 (delete m1 M)). apply delete_intro. auto. 
         intro.  destruct H1. auto. assert(((ida m1) <> (id a))\/(idb m1) <> (id b)).
         left. auto. apply (Qty_delete (delete m2 M) m1 a b) in H6. 
         assert(((ida m2) <> (id a))\/(idb m2) <> (id b)). right. auto.
         apply Qty_delete with (M:=M) in H7. rewrite H6. rewrite H7. auto.
         destruct (Nat.eqb (idb m2) (id b)) eqn:Hm2b;
         destruct (Nat.eqb (ida m1) (id a)) eqn:Hm1a.
         move /eqP in Hm2b. destruct H3. auto. all:simpl;auto.
         destruct (Nat.eqb (id b) (id b)) eqn:Hb; 
         destruct (Nat.eqb (id a) (id a)) eqn:Ha. simpl;auto.
         move /eqP in Ha. destruct Ha. auto. move /eqP in Hb. destruct Hb. auto.
         move /eqP in Ha. destruct Ha. auto.
       }
       { simpl. replace (Nat.eqb (id b) (id b) && Nat.eqb (id a) (id a)) with true.
         replace (Nat.eqb (idb m2) (id b)) with false. simpl. 
         assert(((ida m1) <> (id a))\/(idb m1) <> (id b)).
         left. auto. apply (Qty_delete (delete m2 M) m1 a b) in H6. 
         assert(((ida m2) <> (id a))\/(idb m2) <> (id b)). right. auto.
         apply Qty_delete with (M:=M) in H7. rewrite H6. rewrite H7. auto. symmetry.
         apply /eqP. auto. symmetry.          destruct (Nat.eqb (id b) (id b)) eqn:Hb; 
         destruct (Nat.eqb (id a) (id a)) eqn:Ha. simpl;auto.
         move /eqP in Ha. destruct Ha. auto. move /eqP in Hb. destruct Hb. auto.
         move /eqP in Ha. destruct Ha. auto.
       }
       { simpl. replace (Nat.eqb (id b) (id b) && Nat.eqb (id a) (id a)) with true.
         replace (Nat.eqb (idb m2) (id b)) with false. simpl.
         replace (Nat.eqb (ida m1) (id a)) with false. replace (Nat.eqb (idb m1) (id b)) with true. simpl. 
         assert(((ida m1) <> (id a))\/(idb m1) <> (id b)).
         left. auto. apply (Qty_delete (delete m2 M) m1 a b) in H6. 
         assert(((ida m2) <> (id a))\/(idb m2) <> (id b)). right. auto.
         apply Qty_delete with (M:=M) in H7. rewrite H6. rewrite H7. auto. symmetry.
         apply /eqP. auto. symmetry. apply /eqP. auto. symmetry. apply /eqP. auto.
         destruct (Nat.eqb (id b) (id b)) eqn:Hb; 
         destruct (Nat.eqb (id a) (id a)) eqn:Ha. simpl;auto.
         move /eqP in Ha. destruct Ha. auto. move /eqP in Hb. destruct Hb. auto.
         move /eqP in Ha. destruct Ha. auto.
       }
       {  simpl. replace (Nat.eqb (id b) (id b) && Nat.eqb (id a) (id a)) with true.
         replace (Nat.eqb (idb m2) (id b)) with false. simpl.
         replace (Nat.eqb (ida m1) (id a)) with false. replace (Nat.eqb (idb m1) (id b)) with true. simpl. 
         assert(((ida m1) <> (id a))\/(idb m1) <> (id b)).
         left. auto. apply (Qty_delete (delete m2 M) m1 a b) in H6. 
         assert(((ida m2) <> (id a))\/(idb m2) <> (id b)). right. auto.
         apply Qty_delete with (M:=M) in H7. rewrite H6. rewrite H7. auto. symmetry.
         apply /eqP. auto. symmetry. apply /eqP. auto. symmetry. apply /eqP. auto.
         destruct (Nat.eqb (id b) (id b)) eqn:Hb; 
         destruct (Nat.eqb (id a) (id a)) eqn:Ha. simpl;auto.
         move /eqP in Ha. destruct Ha. auto. move /eqP in Hb. destruct Hb. auto.
         move /eqP in Ha. destruct Ha. auto.
} Qed.

(* Proof that trade quantity of each bid b0 is invariant in increase_ab_quantity *)
Lemma increase_ab_quantity_Qty_bid (M:list transaction)(m1 m2:transaction)(b b0:order)(a:order):
In m1 M ->
In m2 M ->
m1<>m2 ->
(id a) = (ida m2) ->
(id b) = (idb m1) ->
Qty_bid (increase_ab_quantity M m1 m2 b a) (id b0) = Qty_bid M (id b0).
Proof. rewrite increase_ab_quantity_equation_1. intros.
       destruct (Compare_dec.le_lt_dec (tquantity m2) 1) eqn:Hm2;
       destruct (Compare_dec.le_lt_dec (tquantity m1) 1) eqn:Hm1.
       { simpl. assert(tquantity m2 = 1). destruct m2. simpl. simpl in l.
         assert(Ht1:=tquantity_cond).  move /leP in Ht1. lia.
         assert(tquantity m1 = 1). destruct m1. simpl. simpl in l0.
         assert(Ht1:=tquantity_cond).  move /leP in Ht1. lia.
         destruct (Nat.eqb (id b) (id b0)) eqn:Hbb; destruct (Nat.eqb (idb m2) (id b0)) eqn:Hmb.
         + move /eqP in Hbb. move /eqP in Hmb. rewrite <- Hmb. rewrite <- (Qty_bid_delete2 M m2). 
           replace (idb m2) with (idb m1). rewrite <- (Qty_bid_delete2 (delete m2 M) m1). lia.
           apply delete_intro. all:auto. lia.
         + move /eqP in Hbb. move /eqP in Hmb. rewrite <- (Qty_bid_delete1 M m2). 
           replace (id b0) with (idb m1).  rewrite <- (Qty_bid_delete2 (delete m2 M) m1). lia.
           apply delete_intro. all:auto. lia.
         + move /eqP in Hmb. replace (id b0) with (idb m2). rewrite <- (Qty_bid_delete2 M m2). 
           rewrite <- (Qty_bid_delete1 (delete m2 M) m1). lia. all:auto. move /eqP in Hbb. lia.
         + move /eqP in Hmb. move /eqP in Hbb. rewrite <- (Qty_bid_delete1 M m2). 
           rewrite <- (Qty_bid_delete1 (delete m2 M) m1). exact. lia. lia.
        }
        { simpl. assert(tquantity m2 = 1). destruct m2. simpl. simpl in l.
          assert(Ht1:=tquantity_cond).  move /leP in Ht1. lia.
          destruct (Nat.eqb (id b) (id b0)) eqn:Hbb; destruct (Nat.eqb (idb m2) (id b0)) eqn:Hmb.
         + replace (Nat.eqb (idb m1) (id b0)) with true. 
           move /eqP in Hbb. move /eqP in Hmb. rewrite <- Hmb. rewrite <- (Qty_bid_delete2 M m2). 
           replace (idb m2) with (idb m1). rewrite <- (Qty_bid_delete2 (delete m2 M) m1). lia.
           apply delete_intro. all:auto. lia. symmetry. apply /eqP. move /eqP in Hbb. lia.
         + replace (Nat.eqb (idb m1) (id b0)) with true.  move /eqP in Hbb.
           move /eqP in Hmb. rewrite <- (Qty_bid_delete1 M m2). 
           replace (id b0) with (idb m1).  rewrite <- (Qty_bid_delete2 (delete m2 M) m1). lia.
           apply delete_intro. all:auto. lia. symmetry. apply /eqP. move /eqP in Hbb. lia.
         + replace (Nat.eqb (idb m1) (id b0)) with false. 
           move /eqP in Hmb. replace (id b0) with (idb m2). rewrite <- (Qty_bid_delete2 M m2). 
           rewrite <- (Qty_bid_delete1 (delete m2 M) m1). lia. all:auto. move /eqP in Hbb. lia.
           symmetry. apply /eqP. move /eqP in Hbb. lia.
         + replace (Nat.eqb (idb m1) (id b0)) with false. 
           move /eqP in Hmb. move /eqP in Hbb. rewrite <- (Qty_bid_delete1 M m2). 
           rewrite <- (Qty_bid_delete1 (delete m2 M) m1). exact. lia. lia.
           symmetry. apply /eqP. move /eqP in Hbb. lia.
         }
        { simpl. assert(tquantity m1 = 1). destruct m1. simpl. simpl in l0.
          assert(Ht1:=tquantity_cond).  move /leP in Ht1. lia.
          destruct (Nat.eqb (id b) (id b0)) eqn:Hbb; destruct (Nat.eqb (idb m2) (id b0)) eqn:Hmb.
         + move /eqP in Hbb. move /eqP in Hmb. rewrite <- Hmb. rewrite <- (Qty_bid_delete2 M m2). 
           replace (idb m2) with (idb m1). rewrite <- (Qty_bid_delete2 (delete m2 M) m1). lia.
           apply delete_intro. all:auto. lia.
         + move /eqP in Hmb. rewrite <- (Qty_bid_delete1 M m2). 
           replace (id b0) with (idb m1).  rewrite <- (Qty_bid_delete2 (delete m2 M) m1). lia.
           apply delete_intro. all:auto. move /eqP in Hbb. lia.
         + move /eqP in Hmb. replace (id b0) with (idb m2). rewrite <- (Qty_bid_delete2 M m2). 
           rewrite <- (Qty_bid_delete1 (delete m2 M) m1). lia. all:auto. move /eqP in Hbb. lia.
         + move /eqP in Hmb. move /eqP in Hbb. rewrite <- (Qty_bid_delete1 M m2). 
           rewrite <- (Qty_bid_delete1 (delete m2 M) m1). exact. lia. lia.
         }
         { simpl. destruct (Nat.eqb (id b) (id b0)) eqn:Hbb; destruct (Nat.eqb (idb m2) (id b0)) eqn:Hmb.
         + replace (Nat.eqb (idb m1) (id b0)) with true. 
           move /eqP in Hbb. move /eqP in Hmb. rewrite <- Hmb. rewrite <- (Qty_bid_delete2 M m2). 
           replace (idb m2) with (idb m1). rewrite <- (Qty_bid_delete2 (delete m2 M) m1). lia.
           apply delete_intro. all:auto. lia. symmetry. apply /eqP. move /eqP in Hbb. lia.
         + replace (Nat.eqb (idb m1) (id b0)) with true.  move /eqP in Hbb.
           move /eqP in Hmb. rewrite <- (Qty_bid_delete1 M m2). 
           replace (id b0) with (idb m1).  rewrite <- (Qty_bid_delete2 (delete m2 M) m1). lia.
           apply delete_intro. all:auto. lia. symmetry. apply /eqP. move /eqP in Hbb. lia.
         + replace (Nat.eqb (idb m1) (id b0)) with false. 
           move /eqP in Hmb. replace (id b0) with (idb m2). rewrite <- (Qty_bid_delete2 M m2). 
           rewrite <- (Qty_bid_delete1 (delete m2 M) m1). lia. all:auto. move /eqP in Hbb. lia.
           symmetry. apply /eqP. move /eqP in Hbb. lia.
         + replace (Nat.eqb (idb m1) (id b0)) with false. 
           move /eqP in Hmb. move /eqP in Hbb. rewrite <- (Qty_bid_delete1 M m2). 
           rewrite <- (Qty_bid_delete1 (delete m2 M) m1). exact. lia. lia.
           symmetry. apply /eqP. move /eqP in Hbb. lia.
         }
 Qed.

(* Proof that trade quantity of each ask a0 is invariant in increase_ab_quantity *)
Lemma increase_ab_quantity_Qty_ask (M:list transaction)(m1 m2:transaction)(b:order)(a a0:order):
In m1 M ->
In m2 M ->
m1<>m2 ->
(id a) = (ida m2) ->
Qty_ask (increase_ab_quantity M m1 m2 b a) (id a0) = Qty_ask M (id a0).
Proof. rewrite increase_ab_quantity_equation_1. intros.
       destruct (Compare_dec.le_lt_dec (tquantity m2) 1) eqn:Hm2;
       destruct (Compare_dec.le_lt_dec (tquantity m1) 1) eqn:Hm1.
       { simpl. assert(tquantity m2 = 1). destruct m2. simpl. simpl in l.
         assert(Ht1:=tquantity_cond).  move /leP in Ht1. lia.
         assert(tquantity m1 = 1). destruct m1. simpl. simpl in l0.
         assert(Ht1:=tquantity_cond).  move /leP in Ht1. lia.
         destruct (Nat.eqb (id a) (id a0)) eqn:Haa; destruct (Nat.eqb (ida m1) (id a0)) eqn:Hma.
         + replace (id a0) with (ida m2). rewrite <- (Qty_ask_delete2 M m2). 
           replace (ida m2) with (ida m1). rewrite <- (Qty_ask_delete2 (delete m2 M) m1). lia.
           apply delete_intro. all:auto. move /eqP in Haa. move /eqP in Hma. lia.
           move /eqP in Haa. move /eqP in Hma. lia.
         + move /eqP in Haa. move /eqP in Hma. replace (id a0) with (ida m2). rewrite <- (Qty_ask_delete2 M m2). 
           rewrite <- (Qty_ask_delete1 (delete m2 M) m1). lia. all:auto. lia. lia.
         + move /eqP in Haa. move /eqP in Hma. rewrite <- (Qty_ask_delete1 M m2).
           replace (id a0) with (ida m1).  rewrite <- (Qty_ask_delete2 (delete m2 M) m1). lia.
           apply delete_intro. all:auto. lia.
         + move /eqP in Haa. move /eqP in Hma. rewrite <- (Qty_ask_delete1 M m2). 
           rewrite <- (Qty_ask_delete1 (delete m2 M) m1). exact. lia. lia.
        }
        { simpl. assert(tquantity m2 = 1). destruct m2. simpl. simpl in l.
          assert(Ht1:=tquantity_cond).  move /leP in Ht1. lia.
          destruct (Nat.eqb (id a) (id a0)) eqn:Haa; destruct (Nat.eqb (ida m1) (id a0)) eqn:Hma.
         + replace (id a0) with (ida m2). rewrite <- (Qty_ask_delete2 M m2). 
           replace (ida m2) with (ida m1). rewrite <- (Qty_ask_delete2 (delete m2 M) m1). lia.
           apply delete_intro. all:auto. move /eqP in Haa. move /eqP in Hma. lia.
           move /eqP in Haa. move /eqP in Hma. lia.
         + move /eqP in Haa. move /eqP in Hma. replace (id a0) with (ida m2). rewrite <- (Qty_ask_delete2 M m2). 
           rewrite <- (Qty_ask_delete1 (delete m2 M) m1). lia. all:auto. lia. lia.
         + move /eqP in Haa. move /eqP in Hma. rewrite <- (Qty_ask_delete1 M m2).
           replace (id a0) with (ida m1).  rewrite <- (Qty_ask_delete2 (delete m2 M) m1). lia.
           apply delete_intro. all:auto. lia.
         + move /eqP in Haa. move /eqP in Hma. rewrite <- (Qty_ask_delete1 M m2). 
           rewrite <- (Qty_ask_delete1 (delete m2 M) m1). exact. lia. lia.
        }
        { simpl. assert(tquantity m1 = 1). destruct m1. simpl. simpl in l0.
          assert(Ht1:=tquantity_cond).  move /leP in Ht1. lia.
          destruct (Nat.eqb (id a) (id a0)) eqn:Haa; destruct (Nat.eqb (ida m1) (id a0)) eqn:Hma.
         + replace (Nat.eqb (ida m2) (id a0)) with true. replace (id a0) with (ida m2). 
           rewrite <- (Qty_ask_delete2 M m2). 
           replace (ida m2) with (ida m1). rewrite <- (Qty_ask_delete2 (delete m2 M) m1). lia.
           apply delete_intro. all:auto. move /eqP in Haa. move /eqP in Hma. lia.
           move /eqP in Haa. move /eqP in Hma. lia. symmetry. apply /eqP. move /eqP in Haa. lia.
         + move /eqP in Haa. move /eqP in Hma.
           replace (Nat.eqb (ida m2) (id a0)) with true. replace (id a0) with (ida m2). 
           rewrite <- (Qty_ask_delete2 M m2). 
           rewrite <- (Qty_ask_delete1 (delete m2 M) m1). lia. all:auto. 
           lia. lia. symmetry. apply /eqP. lia.
         + move /eqP in Haa. move /eqP in Hma.
           replace (Nat.eqb (ida m2) (id a0)) with false. rewrite <- (Qty_ask_delete1 M m2).
           replace (id a0) with (ida m1).  rewrite <- (Qty_ask_delete2 (delete m2 M) m1). lia.
           apply delete_intro. all:auto. lia. symmetry. apply /eqP. lia.
         + move /eqP in Haa. move /eqP in Hma.
           replace (Nat.eqb (ida m2) (id a0)) with false.
           rewrite <- (Qty_ask_delete1 M m2). 
           rewrite <- (Qty_ask_delete1 (delete m2 M) m1). exact. lia. lia.
           symmetry. apply /eqP. lia.
        }
        { simpl. 
          destruct (Nat.eqb (id a) (id a0)) eqn:Haa; destruct (Nat.eqb (ida m1) (id a0)) eqn:Hma.
         + replace (Nat.eqb (ida m2) (id a0)) with true. replace (id a0) with (ida m2). 
           rewrite <- (Qty_ask_delete2 M m2). 
           replace (ida m2) with (ida m1). rewrite <- (Qty_ask_delete2 (delete m2 M) m1). lia.
           apply delete_intro. all:auto. move /eqP in Haa. move /eqP in Hma. lia.
           move /eqP in Haa. move /eqP in Hma. lia. symmetry. apply /eqP. move /eqP in Haa. lia.
         + move /eqP in Haa. move /eqP in Hma.
           replace (Nat.eqb (ida m2) (id a0)) with true. replace (id a0) with (ida m2). 
           rewrite <- (Qty_ask_delete2 M m2). 
           rewrite <- (Qty_ask_delete1 (delete m2 M) m1). lia. all:auto. 
           lia. lia. symmetry. apply /eqP. lia.
         + move /eqP in Haa. move /eqP in Hma.
           replace (Nat.eqb (ida m2) (id a0)) with false. rewrite <- (Qty_ask_delete1 M m2).
           replace (id a0) with (ida m1).  rewrite <- (Qty_ask_delete2 (delete m2 M) m1). lia.
           apply delete_intro. all:auto. lia. symmetry. apply /eqP. lia.
         + move /eqP in Haa. move /eqP in Hma.
           replace (Nat.eqb (ida m2) (id a0)) with false.
           rewrite <- (Qty_ask_delete1 M m2). 
           rewrite <- (Qty_ask_delete1 (delete m2 M) m1). exact. lia. lia.
           symmetry. apply /eqP. lia.
        } Qed.

Lemma increase_ab_quantity_Uniform (M:list transaction)(m1 m2:transaction)(b:order)(a:order):
In m1 M ->
In m2 M ->
Uniform M ->
Uniform (increase_ab_quantity M m1 m2 b a).
Proof. unfold Uniform. intros. rewrite increase_ab_quantity_equation_1.
       destruct (Compare_dec.le_lt_dec (tquantity m2) 1) eqn:Hm2;
       destruct (Compare_dec.le_lt_dec (tquantity m1) 1) eqn:Hm1.
       { simpl. constructor. auto. apply uniform_intro.
         intros. assert(In x (tprices M)).
         apply tps_of_delete in H2. 
         apply tps_of_delete in H2.
         exact. assert(In (tprice m1) (tprices M)). apply in_map_iff. exists m1. auto.
         apply uniform_elim4 with (l:=tprices M)(a1:=x)(a2:=tprice m2). all:auto.
         apply in_map_iff. exists m2. auto.
       }
       { simpl. constructor. auto. constructor. apply uniform_elim4 with (l:=(tprices M)).
         auto. apply in_map_iff. exists m2. auto. apply in_map_iff. exists m1. auto.
         apply uniform_intro.
         intros. assert(In x (tprices M)).
         apply tps_of_delete in H2. 
         apply tps_of_delete in H2.
         exact. assert(In (tprice m1) (tprices M)). apply in_map_iff. exists m1. auto.
         apply uniform_elim4 with (l:=tprices M)(a1:=x)(a2:=tprice m1). all:auto.
       }
       { simpl. constructor. auto. constructor. apply uniform_elim4 with (l:=(tprices M)).
         auto. apply in_map_iff. exists m2. auto. apply in_map_iff. exists m2. auto.
         apply uniform_intro.
         intros. assert(In x (tprices M)).
         apply tps_of_delete in H2. 
         apply tps_of_delete in H2.
         exact. assert(In (tprice m1) (tprices M)). apply in_map_iff. exists m1. auto.
         apply uniform_elim4 with (l:=tprices M)(a1:=x)(a2:=tprice m2). all:auto.
         apply in_map_iff. exists m2. auto.
       }
       { simpl. constructor. auto. constructor. auto. constructor. apply uniform_elim4 with (l:=(tprices M)).
         auto. apply in_map_iff. exists m2. auto. apply in_map_iff. exists m1. auto.
         apply uniform_intro.
         intros. assert(In x (tprices M)).
         apply tps_of_delete in H2. 
         apply tps_of_delete in H2.
         exact. assert(In (tprice m1) (tprices M)). apply in_map_iff. exists m1. auto.
         apply uniform_elim4 with (l:=tprices M)(a1:=x)(a2:=tprice m1). all:auto.
       } Qed.

Lemma increase_ab_quantity_Matching (M:list transaction)(m1 m2:transaction)(b:order)(a:order)(B A: list order):
In m1 M ->
In m2 M ->
In b B ->
In a A ->
m1<>m2 ->
(id a) = (ida m2) ->
(id b) <> idb m2 ->
(id b) = (idb m1) ->
(id a) <> ida m1 ->
oprice b >= oprice a ->
Matching M B A -> Matching (increase_ab_quantity M m1 m2 b a) B A.
Proof. unfold Matching. unfold Tvalid. unfold valid. intros.
destruct H9. rewrite increase_ab_quantity_equation_1. split. 
  { destruct (Compare_dec.le_lt_dec (tquantity m1) 1) eqn:Hm1;
    destruct (Compare_dec.le_lt_dec (tquantity m2) 1) eqn:Hm2.
    { simpl. intros. destruct H11. subst t. simpl. { exists b. exists a. split. auto.
      split. auto. split. auto. split. auto. split. auto. 
apply H9 in H0. destruct H0. destruct H0. destruct H0. destruct H11. destruct H12. destruct H13. destruct H14.
admit. } 
      destruct H11. subst t. simpl. apply H9 in H as Hm1a. apply H9 in H0 as Hm2b. admit.
      apply delete_elim1 in H11. apply delete_elim1 in H11. apply H9 in H11. auto.
    }
    {simpl. intros. destruct H11. subst t. simpl. exists b. exists a. admit. 
      destruct H11. subst t. simpl. apply H9 in H as Hm1a. apply H9 in H0 as Hm2b. admit.
      destruct H11. subst t. simpl.  apply H9 in H0 as Hm2b. admit.
      apply delete_elim1 in H11. apply delete_elim1 in H11. apply H9 in H11. auto.
    }
    {simpl. intros. destruct H11. subst t. simpl. exists b. exists a. admit. 
      destruct H11. subst t. simpl. apply H9 in H as Hm1a. apply H9 in H0 as Hm2b. admit.
      destruct H11. subst t. simpl.  apply H9 in H as Hm1a. admit.
      apply delete_elim1 in H11. apply delete_elim1 in H11. apply H9 in H11. auto.
    }
    {simpl. intros. destruct H11. subst t. simpl. exists b. exists a. admit. 
      destruct H11. subst t. simpl. apply H9 in H as Hm1a. apply H9 in H0 as Hm2b. admit.
      destruct H11. subst t. simpl.  apply H9 in H0 as Hm2b. admit.
      destruct H11. subst t. simpl.  apply H9 in H as Hm1a. admit.
      apply delete_elim1 in H11. apply delete_elim1 in H11. apply H9 in H11. auto.
    }
  } destruct H10. split. rewrite <- increase_ab_quantity_equation_1. intros. apply H10 in H12.
    rewrite increase_ab_quantity_Qty_bid. all:auto. rewrite <- increase_ab_quantity_equation_1.
    intros. apply H11 in H12. rewrite increase_ab_quantity_Qty_ask. all:auto. Admitted.


Theorem increase_ab_quantity_Is_uniform (M:list transaction)(m1 m2:transaction)
(b:order)(a:order)(B:list order)(A:list order):
In m1 M ->
In m2 M ->
m1<>m2 ->
(id a) = (ida m2) ->
(id b) <> idb m2 ->
(id b) = (idb m1) ->
(id a) <> ida m1 ->
oprice b >= oprice a ->
Is_uniform M (b::B) (a::A) -> Is_uniform (increase_ab_quantity M m1 m2 b a) (b::B) (a::A).
Proof. intros. split. 
      { apply increase_ab_quantity_Uniform. all:auto. apply H7. } 
      { apply increase_ab_quantity_Matching. all:auto. apply H7. } Qed.

(*#######################End of surgery one#########################*) 


(*########Surgery Two############################*)

Equations increase_b_quantity (M:list transaction)(m:transaction)(b:order)(a:order):(list transaction):=  
increase_b_quantity M m b a := 
    (match (Compare_dec.le_lt_dec (tquantity m) 1) with 
        |left _ => ((Mk_transaction (id b) (id a) (oprice a) 1 not1)::(delete m M)) 
        |right _ => ((Mk_transaction (id b) (id a) (oprice a) 1 not1)::
                     (Mk_transaction (idb m) (ida m) (tprice m) (tquantity m - 1) _ )::(delete m M)) end).
Next Obligation.
 apply PeanoNat.Nat.ltb_nlt. lia. Defined.  

Lemma increase_b_quantity_Vol (M:list transaction)
(m:transaction)(b:order)(a:order):
In m M -> Vol(M) = Vol(increase_b_quantity M m b a).
Proof. rewrite increase_b_quantity_equation_1. intros. destruct (Compare_dec.le_lt_dec (tquantity m) 1) eqn:Hm.
simpl. assert(tquantity m = 1). destruct m. simpl. simpl in l. assert(Ht:=tquantity_cond). move /leP in Ht. lia.
apply Vol_delete_m in H. lia. simpl. apply Vol_delete_m in H. lia.  Qed.

(*Proof that in increase_b_quantity, the trade between a and b is increased by single unit.*)
Lemma increase_b_quantity_extra (M:list transaction)(m:transaction)(b:order)(a:order):
In m M ->
(id b) = (idb m) ->
(id a) <> (ida m) ->
Qty (increase_b_quantity M m b a) (id b) (id a) = 1 + Qty M (id b) (id a).
Proof. rewrite increase_b_quantity_equation_1. intros. destruct (Compare_dec.le_lt_dec (tquantity m) 1) eqn:Hm.
simpl. assert(tquantity m = 1). destruct m. simpl. simpl in l. assert(Ht:=tquantity_cond). move /leP in Ht. lia.
replace (Nat.eqb (id b) (id b) && Nat.eqb (id a) (id a)) with true. 
rewrite Qty_delete. auto. auto. symmetry. apply /andP.  split. auto. auto. 
simpl. replace (Nat.eqb (id b) (id b) && Nat.eqb (id a) (id a)) with true. 
replace (Nat.eqb (idb m) (id b) && Nat.eqb (ida m) (id a)) with false. 
rewrite Qty_delete. auto. auto. symmetry. apply /andP. intro. destruct H2.
move /eqP in H3. destruct H1. auto. symmetry. apply /andP.  split. auto. auto.  Qed.


(*Proof that trade fill of bid b is invariant in g*)
Lemma increase_b_quantity_Qty_bid (M:list transaction)(m:transaction)(b b0:order)(a:order):
In m M ->
id b = idb m ->
Qty_bid (increase_b_quantity M m b a) (id b0) = Qty_bid M (id b0).
Proof. rewrite increase_b_quantity_equation_1. intros. destruct (Compare_dec.le_lt_dec (tquantity m) 1) eqn:Hm.
simpl. assert(tquantity m = 1). destruct m. simpl. simpl in l. assert(Ht:=tquantity_cond). move /leP in Ht. lia.
destruct (Nat.eqb (id b) (id b0)) eqn:Hbb. apply Qty_bid_delete2 in H.
replace (idb m) with (id b0) in H. lia. move /eqP in Hbb. lia. rewrite Qty_bid_delete1.
 move /eqP in Hbb. lia. exact. simpl. destruct (Nat.eqb (id b) (id b0)) eqn:Hbb. 
replace (Nat.eqb (idb m) (id b0)) with true. apply Qty_bid_delete2 in H. 
replace (idb m) with (id b0) in H. lia. move /eqP in Hbb. lia. symmetry.
move /eqP in Hbb. apply /eqP. lia. replace (Nat.eqb (idb m) (id b0)) with false.
apply Qty_bid_delete1. move /eqP in Hbb. lia. symmetry.
move /eqP in Hbb. apply /eqP. lia. Qed. 

(* Proof that trade fill of ask a0 is invariant in g *)
Lemma increase_b_quantity_Qty_ask (M:list transaction)(m:transaction)(b:order)(a a0:order):
In m M ->
(id a0) <> (id a) ->
(id a0) <> (ida m) ->
Qty_ask (increase_b_quantity M m b a) (id a0) = Qty_ask M (id a0).
Proof. rewrite increase_b_quantity_equation_1. intros. destruct (Compare_dec.le_lt_dec (tquantity m) 1) eqn:Hm.
simpl. assert(tquantity m = 1). destruct m. simpl. simpl in l. assert(Ht:=tquantity_cond). move /leP in Ht. lia.
replace (Nat.eqb (id a) (id a0)) with false. rewrite Qty_ask_delete1. auto. auto.
symmetry.  apply /eqP. lia. simpl. replace (Nat.eqb (id a) (id a0)) with false.
replace (Nat.eqb (ida m) (id a0)) with false. rewrite Qty_ask_delete1. auto. auto.
symmetry. apply /eqP. auto. symmetry. apply /eqP. auto. Qed.

(* Proof that quantity ask a is increased by one *)
Lemma increase_b_quantity_Qty_ask_a (M:list transaction)(m:transaction)(b:order)(a:order):
In m M ->
(id a) <> (ida m) ->
Qty_ask (increase_b_quantity M m b a) (id a) = 1 + Qty_ask M (id a).
Proof. rewrite increase_b_quantity_equation_1. intros. destruct (Compare_dec.le_lt_dec (tquantity m) 1) eqn:Hm.
simpl. assert(tquantity m = 1). destruct m. simpl. simpl in l. assert(Ht:=tquantity_cond). move /leP in Ht. lia.
replace (Nat.eqb (id a) (id a)) with true. rewrite Qty_ask_delete1. auto. auto.
symmetry.  apply /eqP. lia. simpl. replace (Nat.eqb (id a) (id a)) with true.
replace (Nat.eqb (ida m) (id a)) with false. rewrite Qty_ask_delete1. auto. auto.
symmetry. apply /eqP. auto. symmetry. apply /eqP. auto. Qed.

(* Proof that quantity (ida m) is decreased by one *)
Lemma increase_b_quantity_Qty_ask_ida_m (M:list transaction)(m:transaction)(b:order)(a:order):
In m M ->
(id a) <> (ida m) ->
1+ Qty_ask (increase_b_quantity M m b a) (ida m) = Qty_ask M (ida m).
Proof. rewrite increase_b_quantity_equation_1. intros. destruct (Compare_dec.le_lt_dec (tquantity m) 1) eqn:Hm.
simpl. assert(tquantity m = 1). destruct m. simpl. simpl in l. assert(Ht:=tquantity_cond). move /leP in Ht. lia.
replace (Nat.eqb (id a) (ida m)) with false. apply Qty_ask_delete2 in H. lia. auto.
simpl. replace (Nat.eqb (id a) (ida m)) with false.
replace (Nat.eqb (ida m) (ida m)) with true. apply Qty_ask_delete2 in H. lia. auto.
symmetry. apply /eqP. auto. Qed.

Lemma increase_b_quantity_Tvalid (M:list transaction)(m:transaction)(b:order)(a:order)(B A: list order):
In m M ->
(id b) = (idb m) ->
(id a) <> (ida m) ->
oprice b >= oprice a ->
Tvalid M (b::B) (a::A) -> Tvalid (increase_b_quantity M m b a) (b::B) (a::A).
Proof. unfold Tvalid. unfold valid. rewrite increase_b_quantity_equation_1. intros. 
destruct (Compare_dec.le_lt_dec (tquantity m) 1) eqn:Hm.
{ simpl. assert(tquantity m = 1). destruct m. simpl. simpl in l. assert(Ht:=tquantity_cond). move /leP in Ht. lia.
  simpl in H4. destruct H4.
    + subst t. simpl. exists b. exists a. split. auto. split. auto. split. auto. split. auto.
      split. auto. split. destruct b. simpl. assert(Ht:=oquantity_cond). move /leP in Ht. lia.
      split. destruct a. simpl. assert(Ht:=oquantity_cond). move /leP in Ht. lia. auto. 
    + apply delete_elim1 in H4. apply H3 in H4. auto.
}
{ simpl in H4. destruct H4.
    + subst t. simpl. exists b. exists a. split. auto. split. auto. split. auto. split. auto. split. auto. split.
      destruct b. simpl. assert(Ht:=oquantity_cond). move /leP in Ht. lia. split. destruct a. simpl.
      assert(Ht:=oquantity_cond). move /leP in Ht. lia. auto. 
    + destruct H4.
      ++ subst t. simpl. apply H3 in H. destruct H as [b0 H]. destruct H as [a0 H]. exists b0. exists a0.
         split. apply H. split. apply H.  split. apply H. split. apply H.  split. apply H.  split.
         cut(tquantity m <= oquantity b0). lia. apply H. cut (tquantity m <= oquantity a0). lia.
         apply H.
      ++ apply delete_elim1 in H4. apply H3 in H4. auto.
} Qed. 

Lemma increase_b_quantity_Matching (M:list transaction)(m:transaction)(b:order)(a:order)(B A: list order):
NoDup (ids (a::A)) ->
In m M ->
(id b) = (idb m) ->
(id a) <> (ida m) ->
oprice b >= oprice a ->
Qty_ask M (id a) < oquantity a ->
Matching M (b::B) (a::A) -> Matching (increase_b_quantity M m b a) (b::B) (a::A).
Proof. unfold Matching. intros. split. apply increase_b_quantity_Tvalid. all:auto. apply H5.
split. intros. rewrite increase_b_quantity_Qty_bid. all:auto. apply H5. auto. intros.
simpl in H6. destruct H6. subst a0. rewrite increase_b_quantity_Qty_ask_a. all:auto.
destruct (Nat.eqb (id a0) (ida m)) eqn:Hma. move /eqP in Hma. 
cut(Qty_ask M (id a0) <= oquantity a0). rewrite Hma. rewrite <- (increase_b_quantity_Qty_ask_ida_m M m b a).
 lia. all:auto. apply H5. simpl. right. auto. move /eqP in Hma. rewrite increase_b_quantity_Qty_ask.
all:auto. simpl in H. apply NoDup_cons_iff in H. destruct H. intro. apply ids_intro in H6.
rewrite H8 in H6. eauto. apply H5. simpl. right. auto. Qed. 
 
(*#######################End of surgery Two########################*)

(************************************************************************)

(*########Surgeries for the existence of M'  = M - q matchings ############*)

(* This function removes trades for a given pair of bid and ask. 
This is used in the proofs maximality for MM and UM. We claim that
given a matching M there exists another matching M' in the reduced list of
Bids and Asks such that the size of M' is equal to size of M minus q, 
where q is quanity traded between the a pair of bid and ask. *)



(**************** case when the bid and ask are fully traded **********************)


Fixpoint delete_ba_M (M:list transaction)(nb na:nat) :=
match M with 
| nil => nil
| m::M' => match (Nat.eqb (idb m) nb && Nat.eqb (ida m) na) with 
      |true => delete_ba_M M' nb na
      |false => m::(delete_ba_M M' nb na)
    end
end.

Definition nbool b:= if b then false else true.

Definition remove_ab_transactions M nb na := 
filter (fun x:transaction => nbool (Nat.eqb (idb x) nb && Nat.eqb (ida x) na)) M.


Lemma test M nb na: 
delete_ba_M M nb na = remove_ab_transactions M nb na.
Proof. revert nb na. induction M. simpl. auto. simpl. intros.
destruct (Nat.eqb (idb a) nb && Nat.eqb (ida a) na ) eqn:H1. unfold nbool. apply IHM.
unfold nbool. f_equal. apply IHM. Qed.

Lemma remove_ab_transactions_Qty M nb na:
Qty (remove_ab_transactions M nb na) nb na = 0.
Proof. induction M as [|m M']. simpl. auto.
simpl. destruct (Nat.eqb (idb m) nb && Nat.eqb (ida m) na ) eqn:H. unfold nbool.
apply IHM'. simpl. rewrite H. apply IHM'. Qed.


(*Move this lemma to earlier file: This is general and basic lemma *)
Lemma filter_Uniform (M:list transaction)(f:transaction->bool) :
Uniform M -> Uniform (filter f M).
Proof. unfold Uniform. induction M as [|m M'].
simpl. auto. simpl. intros. destruct (f m) eqn:Hab.
simpl. apply uniform_intro. intros. apply uniform_elim with (x:=x) in H.
auto. apply in_map_iff in H0. destruct H0. destruct H0.
apply filter_In in H1. destruct H1. apply in_map_iff.
exists x0. auto. apply uniform_elim2 in H. apply IHM'. auto. Qed.

Lemma remove_ab_transactions_Uniform M nb na:
Uniform M -> Uniform (remove_ab_transactions M nb na).
Proof. apply filter_Uniform. Qed.

Lemma remove_ab_transactions_Vol M nb na:
Vol M = Vol (remove_ab_transactions M nb na) + Qty M nb na.
Proof. induction M. simpl. auto. simpl. destruct ((Nat.eqb (idb a) nb && Nat.eqb (ida a) na)).
simpl. lia. simpl. lia. Qed.

(*
Equations reduced (A B: list order):list order:= 
reduced A B := match (B, A) with
|(_, nil) => nil
|(nil, A) => A
|(b::B, a::A) => match ((Compare_dec.le_lt_dec (oquantity a) (oquantity b))) with
    |left _ => A
    |right _ => ((Mk_order (id a) (otime a) (oquantity a - oquantity b) (oprice a) _ ) :: A)
end end.
Next Obligation.
 apply PeanoNat.Nat.ltb_nlt. apply liaforrun;auto. Defined. *)


Lemma remove_ab_transactions_Qty_full_b M b a t:
Qty_bid M (id b) <= Qty M (id b) (id a) ->
In t (remove_ab_transactions M (id b) (id a)) -> (idb t) <> (id b).
Proof. induction M as [|m M]. simpl. auto. simpl. 
destruct (Nat.eqb (idb m) (id b)) eqn:Hb;destruct (Nat.eqb (ida m) (id a)) eqn:Ha.
{ simpl. intros. apply IHM. lia. auto. }
{ simpl. intros. assert(Qty M (id b) (id a) <= Qty_bid M (id b)).
apply Qty_le_Qty_bid. assert(tquantity m > 0). destruct m. simpl. 
assert(Ht:=tquantity_cond). move /ltP in Ht. lia. lia. }
{ simpl. intros. destruct H0. subst. move /eqP in Hb. auto. apply IHM. all:auto. }
{ simpl. intros. destruct H0. subst. move /eqP in Hb. auto. apply IHM. all:auto. } Qed.

Lemma remove_ab_transactions_Qty_full_a M b a t:
Qty_ask M (id a) <= Qty M (id b) (id a) ->
In t (remove_ab_transactions M (id b) (id a)) -> (ida t) <> (id a).
Proof.  induction M as [|m M]. simpl. auto. simpl. 
destruct (Nat.eqb (idb m) (id b)) eqn:Hb;destruct (Nat.eqb (ida m) (id a)) eqn:Ha.
{ simpl. intros. apply IHM. lia. auto. }
{ simpl. intros. destruct H0. subst. move /eqP in Ha. auto. apply IHM. all:auto. }
{ simpl. intros. assert(Qty M (id b) (id a) <= Qty_ask M (id a)).
apply Qty_le_Qty_ask. assert(tquantity m > 0). destruct m. simpl. 
assert(Ht:=tquantity_cond). move /ltP in Ht. lia. lia. }
{ simpl. intros. destruct H0. subst. move /eqP in Ha. auto. apply IHM. all:auto. } Qed.


(*Lemma remove_ab_transactions_tradeb M B0 A0 b a t:
Matching M (b :: B0) (a :: A0) ->
oquantity a < oquantity b ->
In t (remove_ab_transactions M (id b) (id a)) -> 
idb t = id b ->
tquantity t <= oquantity b - Qty M (id b) (id a).
Proof. revert A0 A0 b a t. induction M as [|m M]. firstorder. simpl.
intros. destruct (Nat.eqb (idb m) (id b)) eqn:Hb;destruct (Nat.eqb (ida m) (id a)) eqn:Ha.
{ simpl. simpl in H1. 

 assert(In m (m::M)). auto. apply H in H4.
unfold valid in H4. destruct H4. destruct H4.
intros. assert(Qty_bid M (id b) >= Qty M (id b) (id a)). admit. 
apply IHM in H0. assert(tquantity m <= oquantity b). admit.
assert(tquantity m <= oquantity a). admit. 
lia. auto. auto. }
{ simpl. intros. destruct H0. move /eqP in Hb. move /eqP in Ha. subst t.
assert(Qty M (id b) (id a) <= Qty_bid M (id b)).
apply Qty_le_Qty_bid. assert(tquantity m > 0). destruct m. simpl. 
assert(Ht:=tquantity_cond). move /ltP in Ht. lia. lia. }
{ simpl. intros. destruct H0. subst. move /eqP in Hb. auto. apply IHM. all:auto. }
{ simpl. intros. destruct H0. subst. move /eqP in Hb. auto. apply IHM. all:auto. } Qed.


Lemma remove_ab_transactions_tradea M b a t:
oquantity b < oquantity a ->
In t (remove_ab_transactions M (id b) (id a)) -> tquantity t <= oquantity a - oquantity b.

*)


(*
Lemma remove_ab_transactions_conservation_bid M b a bi: 
Qty_bid M bi - Qty M (id b) (id a) <= Qty_bid (remove_ab_transactions M (id b) (id a)) bi.
Proof. induction M as [|m M]. simpl. auto. simpl. 
destruct (Nat.eqb (idb m) bi) eqn:Hb;destruct (Nat.eqb (idb m) (id b) && Nat.eqb (ida m) (id a)) eqn:Ha.
{ simpl. lia. }
{ simpl. rewrite Hb.  lia. }
{ simpl. lia. }
{ simpl. rewrite Hb. lia. } Qed.
*)

Lemma remove_ab_transactions_conservation_bid M b a: 
Qty_bid M (id b) - Qty M (id b) (id a) = Qty_bid (remove_ab_transactions M (id b) (id a)) (id b).
Proof. induction M as [|m M]. simpl. auto. simpl. 
destruct (Nat.eqb (idb m) (id b) && Nat.eqb (ida m) (id a)) eqn:Ha.
{ simpl. replace (Nat.eqb (idb m) (id b)) with true. lia. move /andP in Ha. destruct Ha. symmetry.  apply /eqP. 
move /eqP in H. auto. }
{ simpl. destruct (Nat.eqb (idb m) (id b)) eqn:Hb.
    + assert( Qty M (id b) (id a) <= Qty_bid M (id b)). apply Qty_le_Qty_bid.
      lia.
    + auto.  
} Qed.

Lemma remove_ab_transactions_conservation_ask M b a: 
Qty_ask M (id a) - Qty M (id b) (id a) = Qty_ask (remove_ab_transactions M (id b) (id a)) (id a).
Proof. induction M as [|m M]. simpl. auto. simpl. 
destruct (Nat.eqb (idb m) (id b) && Nat.eqb (ida m) (id a)) eqn:Ha.
{ simpl. replace (Nat.eqb (ida m) (id a)) with true. lia. move /andP in Ha. destruct Ha. symmetry.  apply /eqP. 
move /eqP in H0. auto. }
{ simpl. destruct (Nat.eqb (ida m) (id a)) eqn:Hb.
    + assert( Qty M (id b) (id a) <= Qty_ask M (id a)). apply Qty_le_Qty_ask.
      lia.
    + auto.  
} Qed.





Definition reduced (A0 B0: list order)(b a :order):(list order)*(list order).
refine( match (Compare_dec.lt_eq_lt_dec (oquantity a) (oquantity b)) with 
        (*bq=ba*) 
|inleft (right _) => (B0, A0)
(*bq>ba*)

 |inright _ => (B0, ((Mk_order (id a) (otime a) (oquantity a - oquantity b) (oprice a) (Match.Match_obligations_obligation_4 b a _) )::A0))
 
(*bq < ba*)
 |inleft (left _) => (((Mk_order (id b) (otime b) (oquantity b - oquantity a) (oprice b) (Match.Match_obligations_obligation_1 b a _) )::B0), A0) end ).
auto. auto. Defined.

Lemma remove_ab_transactions_main M B0 A0 b a:
uniform (tprices M) ->
Matching M (b :: B0) (a :: A0) ->
Qty M (id b) (id a) = (Nat.min (oquantity b) (oquantity a)) ->
exists OPT, (Is_uniform OPT (fst (reduced A0 B0 b a)) (snd (reduced A0 B0 b a)))/\
        (Vol(M) = Vol(OPT) + Nat.min (oquantity b) (oquantity a)).
Proof. 
intros. exists (remove_ab_transactions M (id b) (id a)).
unfold reduced.
destruct (Compare_dec.lt_eq_lt_dec (oquantity a) (oquantity b) ) eqn:Hab.
{ destruct s eqn:Hs.
{ simpl. replace (Nat.min (oquantity b) (oquantity a)) with (oquantity a). 
  replace (Nat.min (oquantity b) (oquantity a)) with (oquantity a) in H1. split. split. 
  apply remove_ab_transactions_Uniform. apply H. split. unfold Tvalid. intros. apply filter_In in H2 as H3M.
  destruct H3M. unfold nbool in H4. destruct (Nat.eqb (idb t) (id b) && Nat.eqb (ida t) (id a)) eqn:H6.
  inversion H4. apply H0 in H3. unfold valid in H3. destruct H3 as [b0 H3]. destruct H3 as [a0 H5].
  destruct H5. destruct H5. destruct H7. destruct H8. simpl in H3. simpl in H5. assert((ida t) <> (id a)).
  apply remove_ab_transactions_Qty_full_a with (M:=M)(a:=a)(b:=b). assert(Qty_ask M (id a) <= oquantity a).
  apply H0. auto. lia. auto. destruct H3. { subst. lia. }
  { subst. destruct H5. {  subst b0. unfold valid. simpl. 
    exists ({|
     id := id b;
     otime := otime b;
     oquantity := oquantity b - oquantity a;
     oprice := oprice b;
     oquantity_cond := Match.Match_obligations_obligation_1 b a l
   |}). simpl. exists a0. split. auto. split. auto.
    split. auto. split. auto. split. unfold tradable. simpl. apply H9. split. 
assert(Qty_bid M (id b) - Qty M (id b) (id a) = Qty_bid (remove_ab_transactions M (id b) (id a)) (id b)).
apply remove_ab_transactions_conservation_bid. assert(Qty_bid M (id b) <= oquantity b). apply H0. auto.
assert(Qty_bid (remove_ab_transactions M (id b) (id a)) (id b) <= oquantity b - Qty M (id b) (id a)).
lia. rewrite H1 in H12. assert(tquantity t <= Qty_bid (remove_ab_transactions M (id b) (id a)) (id b) \/
tquantity t > Qty_bid (remove_ab_transactions M (id b) (id a)) (id b)). lia. destruct H13. lia.
assert(Qty_bid (remove_ab_transactions M (id b) (id a)) (idb t) >= tquantity t). apply Qty_bid1. auto.
rewrite H7 in H14. lia. split. apply H9. apply H9. }
    { exists b0. exists a0. auto. } } split. intros. simpl in H2. destruct H2. { subst b0. simpl. 
      rewrite <-remove_ab_transactions_conservation_bid. rewrite H1. assert(Qty_bid M (id b) <= oquantity b).
apply H0. auto. lia. }
    { assert(Qty_bid (remove_ab_transactions M (id b) (id a)) (id b0) <= Qty_bid M (id b0)).  apply Qty_bid_filter.
    cut (Qty_bid M (id b0) <= oquantity b0). lia. apply H0. auto. }
    intros. assert(Qty_ask (remove_ab_transactions M (id b) (id a)) (id a0) <= Qty_ask M (id a0)).
    apply Qty_ask_filter. cut (Qty_ask M (id a0) <= oquantity a0). lia. apply H0. auto. 
    rewrite (remove_ab_transactions_Vol M (id b) (id a)). lia. lia. lia. } 
{ assert(oquantity a = oquantity b). lia. replace (Nat.min (oquantity b) (oquantity a)) with (oquantity b). 
  replace (Nat.min (oquantity b) (oquantity a)) with (oquantity b) in H1. split. split. 
  apply remove_ab_transactions_Uniform. apply H. split. unfold Tvalid. intros. apply filter_In in H3 as H3M.
  destruct H3M. unfold nbool in H5. destruct (Nat.eqb (idb t) (id b) && Nat.eqb (ida t) (id a)) eqn:H6.
  inversion H5. apply H0 in H4. unfold valid in H4. destruct H4 as [b0 H4]. destruct H4 as [a0 H4].
  destruct H4. destruct H7. destruct H8. destruct H9. simpl in H4. simpl in H7. assert((ida t) <> (id a)).
  apply remove_ab_transactions_Qty_full_a with (M:=M)(a:=a)(b:=b). assert(Qty_ask M (id a) <= oquantity a).
  apply H0. auto. lia. auto. assert((idb t) <> (id b)).
  apply remove_ab_transactions_Qty_full_b with (M:=M)(a:=a)(b:=b). assert(Qty_bid M (id b) <= oquantity b).
  apply H0. auto. lia. auto. destruct H4;destruct H7. subst. lia. subst. lia. subst. lia.
  exists b0. exists a0. auto. split. intros. 
  assert(Qty_bid (remove_ab_transactions M (id b) (id a)) (id b0) <= Qty_bid M (id b0)).  
  apply Qty_bid_filter. cut (Qty_bid M (id b0) <= oquantity b0). lia. apply H0. auto. intros.
  assert(Qty_ask (remove_ab_transactions M (id b) (id a)) (id a0) <= Qty_ask M (id a0)).  apply Qty_ask_filter.
  cut (Qty_ask M (id a0) <= oquantity a0). lia. apply H0. auto.
  rewrite (remove_ab_transactions_Vol M (id b) (id a)). lia. lia. lia. } }
  { replace (Nat.min (oquantity b) (oquantity a)) with (oquantity b). 
  replace (Nat.min (oquantity b) (oquantity a)) with (oquantity b) in H1. split. split. 
  apply remove_ab_transactions_Uniform. apply H. split. unfold Tvalid. intros. apply filter_In in H2 as H3M.
  destruct H3M. unfold nbool in H4. destruct (Nat.eqb (idb t) (id b) && Nat.eqb (ida t) (id a)) eqn:H6.
  inversion H4. apply H0 in H3. unfold valid in H3. destruct H3 as [b0 H3]. destruct H3 as [a0 H5].
  destruct H5. destruct H5. destruct H7. destruct H8. simpl in H3. simpl in H5. assert((idb t) <> (id b)).
  apply remove_ab_transactions_Qty_full_b with (M:=M)(a:=a)(b:=b). assert(Qty_bid M (id b) <= oquantity b).
  apply H0. auto. lia. auto. destruct H5. { subst. lia. }
  { subst. destruct H3. {  subst a0. unfold valid. simpl. exists b0. 
    exists ({|
     id := id a;
     otime := otime a;
     oquantity := oquantity a - oquantity b;
     oprice := oprice a;
     oquantity_cond := Match.Match_obligations_obligation_4 b a l
   |}). simpl. split. auto. split. auto.
    split. auto. split. auto. split. unfold tradable. simpl. apply H9. split. apply H9. split. 
assert(Qty_ask M (id a) - Qty M (id b) (id a) = Qty_ask (remove_ab_transactions M (id b) (id a)) (id a)).
apply remove_ab_transactions_conservation_ask. assert(Qty_ask M (id a) <= oquantity a). apply H0. auto.
assert(Qty_ask (remove_ab_transactions M (id b) (id a)) (id a) <= oquantity a - Qty M (id b) (id a)).
lia. rewrite H1 in H12. assert(tquantity t <= Qty_ask (remove_ab_transactions M (id b) (id a)) (id a) \/
tquantity t > Qty_ask (remove_ab_transactions M (id b) (id a)) (id a)). lia. destruct H13. lia.
assert(Qty_ask (remove_ab_transactions M (id b) (id a)) (ida t) >= tquantity t). apply Qty_ask1. auto.
rewrite H8 in H14. lia. split. apply H9. apply H9. }
    { simpl. unfold valid. exists b0. exists a0. auto. } } split. intros. 
      assert(Qty_bid (remove_ab_transactions M (id b) (id a)) (id b0) <= Qty_bid M (id b0)).
    apply Qty_bid_filter. cut (Qty_bid M (id b0) <= oquantity b0). lia. apply H0. auto.
    intros. simpl in H2. destruct H2. { subst a0. simpl. rewrite <-remove_ab_transactions_conservation_ask. 
    rewrite H1. assert(Qty_ask M (id a) <= oquantity a). apply H0. auto. lia. }    { assert(Qty_ask (remove_ab_transactions M (id b) (id a)) (id a0) <= Qty_ask M (id a0)).  apply Qty_ask_filter.
    cut (Qty_ask M (id a0) <= oquantity a0). lia. apply H0. auto. } 
    rewrite (remove_ab_transactions_Vol M (id b) (id a)). lia. lia. lia. }
Qed.


Lemma remove_ab_transactions_main_equal M B0 A0 b a:
uniform (tprices M) ->
Matching M (b :: B0) (a :: A0) ->
(oquantity b) = (oquantity a) ->
Qty M (id b) (id a) = (oquantity a) ->
exists OPT, (Is_uniform OPT B0 A0)/\
        (Vol(M) = Vol(OPT) + (oquantity a)).
Proof. intros. apply remove_ab_transactions_main in H0. destruct H0 as [M0 H0].
unfold reduced in H0.
destruct (Compare_dec.lt_eq_lt_dec (oquantity a) (oquantity b)) eqn:Hba. 
destruct s. lia. simpl in H0.
exists M0. split. apply H0. replace (Nat.min (oquantity b) (oquantity a)) with (oquantity a) in H0. 
  apply H0. lia. lia. auto. lia. Qed.


End Transform.

(*

Lemma Remove_ab_trades_elim1 (M:list transaction)(b:order)(a:order)(m:transaction):
In m (Remove_ab_trades M b a) -> In m M.
Proof. induction M as [|m' M']. simpl. auto.
simpl. destruct (a_eqb a (ask_of m') && b_eqb b (bid_of m')) eqn:H.
intros. right. apply IHM'. auto. simpl. intros.
destruct H0. auto. auto. Qed.

Lemma Remove_ab_trades_intro1 (M:list transaction)(b:order)(a:order)(m:transaction):
~In m M -> ~In m (Remove_ab_trades M b a).
Proof. induction M as [|m' M']. simpl. auto.
simpl. destruct (a_eqb a (ask_of m') && b_eqb b (bid_of m')) eqn:H.
intros. apply IHM'. eauto. intros.
simpl. intro. destruct H1. subst m. eauto.
assert(~ In m (Remove_ab_trades M' b a)).
apply IHM'. eauto. auto. Qed.


Lemma Remove_ab_trades_correct1 (M:list transaction)(b:order)(a:order) :
ttq_ab (Remove_ab_trades M b a) b a =0.
Proof. induction M as [|m M']. simpl. auto.
simpl. destruct (a_eqb a (ask_of m) && b_eqb b (bid_of m)) eqn:H.
apply IHM'. simpl. rewrite H. apply IHM'. Qed.

Lemma Remove_ab_trades_correct2a (M:list transaction)(b:order)(a:order) :
ttqa M a = ttq_ab M b a + ttqa (Remove_ab_trades M b a) a.
Proof. induction M as [|m M']. simpl. auto.
simpl. destruct (a_eqb a (ask_of m) && b_eqb b (bid_of m)) eqn:Hab.
{
  destruct (a_eqb a (ask_of m)) eqn: Ha;destruct (b_eqb b (bid_of m)) eqn: Hb.
  { rewrite IHM'. lia. } 
  { simpl in Hab. auto. }
  { simpl in Hab. auto. }
  { simpl in Hab. auto. }
}
{
  destruct (a_eqb a (ask_of m)) eqn: Ha;destruct (b_eqb b (bid_of m)) eqn: Hb.
  { simpl in Hab. symmetry in Hab. auto. }
  { simpl. rewrite Ha. rewrite IHM'.  lia. } 
  {  simpl. rewrite Ha. rewrite IHM'.  lia. }
  {  simpl. rewrite Ha. rewrite IHM'.  lia. }
} Qed.

Lemma Remove_ab_trades_correct2b (M:list transaction)(b:order)(a:order) :
ttqb M b = ttq_ab M b a + ttqb (Remove_ab_trades M b a) b.
Proof. induction M as [|m M']. simpl. auto.
simpl. destruct (a_eqb a (ask_of m) && b_eqb b (bid_of m)) eqn:Hab.
{
  destruct (a_eqb a (ask_of m)) eqn: Ha;destruct (b_eqb b (bid_of m)) eqn: Hb.
  { rewrite IHM'. lia. } 
  { simpl in Hab. auto. }
  { simpl in Hab. auto. }
  { simpl in Hab. auto. }
}
{
  destruct (a_eqb a (ask_of m)) eqn: Ha;destruct (b_eqb b (bid_of m)) eqn: Hb.
  { simpl in Hab. symmetry in Hab. auto. }
  { simpl. rewrite Hb. rewrite IHM'.  lia. } 
  {  simpl. rewrite Hb. rewrite IHM'.  lia. }
  {  simpl. rewrite Hb. rewrite IHM'.  lia. }
} Qed.

Lemma Remove_ab_trades_NZT (M:list transaction)(b:order)(a:order) 
(NZT: forall m : transaction, In m M -> tquantity m > 0):
forall m : transaction, In m (Remove_ab_trades M b a) -> tquantity m > 0.
Proof. intros. assert(In m M \/ ~In m M). eauto.
destruct H0. apply NZT in H0. auto. 
apply Remove_ab_trades_intro1 with (b:=b)(a:=a) in H0. 
unfold not in H0. apply H0 in H. elim H. Qed.

Lemma Remove_ab_trades_matchable (M:list transaction)(b:order)(a:order) :
All_matchable M -> All_matchable (Remove_ab_trades M b a).
Proof. induction M as [|m M']. simpl. auto.
simpl. destruct (a_eqb a (ask_of m) && b_eqb b (bid_of m)) eqn:Hab.
{
  unfold All_matchable. simpl. intros H m' Hm'.
  specialize (H m') as Hm1'. destruct Hm1'. right. 
  eapply Remove_ab_trades_elim1. eauto.
  unfold All_matchable in IHM'. eapply IHM' in Hm'.
  auto. intros. apply H. right. auto. lia.
} 
{
  unfold All_matchable. simpl. intros H m' Hm'. destruct Hm'.
  apply H. auto. apply H. right. eapply Remove_ab_trades_elim1.
  eauto.
} Qed.

Lemma Remove_ab_trades_ttq_le_a (M:list transaction)(b:order)(a a0:order):
ttqa (Remove_ab_trades M b a) a0 <= ttqa M a0.
Proof. induction M as [|m M']. simpl. auto.
simpl. destruct ((a_eqb a (ask_of m)) && (b_eqb b (bid_of m))) eqn:Hab.
{ destruct ((a_eqb a0 (ask_of m))) eqn: Ha0. 
  {
    destruct (a_eqb a a0) eqn:Haa0.
    { move /eqP in Haa0. subst a0. 
      assert(ttqa M' a = ttq_ab M' b a + ttqa (Remove_ab_trades M' b a) a).
      eapply Remove_ab_trades_correct2a.
      rewrite H. lia.
    }
    { move /eqP in Haa0. 
      destruct(a_eqb a (ask_of m)) eqn: Hf.
      move /eqP in Ha0.
      move /eqP in Hf.
      subst a. subst a0. elim Haa0. auto.
      simpl in Hab. inversion Hab.
     }
   }
   {
   apply IHM'.
   }
 }
 { destruct ((a_eqb a0 (ask_of m))) eqn: Ha0. 
  {
    simpl. rewrite Ha0. lia. 
  }
  { simpl. rewrite Ha0. lia.
  }
 } Qed.


Lemma Remove_ab_trades_ttq_le_b (M:list transaction)(b b0:order)(a:order):
ttqb (Remove_ab_trades M b a) b0 <= ttqb M b0.
Proof. induction M as [|m M']. simpl. auto.
simpl. destruct ((a_eqb a (ask_of m)) && (b_eqb b (bid_of m))) eqn:Hab.
{ destruct ((b_eqb b0 (bid_of m))) eqn: Hb0. 
  {
    destruct (b_eqb b b0) eqn:Hbb0.
    { move /eqP in Hbb0. subst b0. 
      assert(ttqb M' b = ttq_ab M' b a + ttqb (Remove_ab_trades M' b a) b).
      eapply Remove_ab_trades_correct2b.
      rewrite H. lia.
    }
    { move /eqP in Hbb0. 
      destruct(b_eqb b (bid_of m)) eqn: Hf.
      move /eqP in Hb0.
      move /eqP in Hf.
      subst b. subst b0. elim Hbb0. auto.
      destruct (a_eqb a (ask_of m)).
      simpl in Hab. inversion Hab.
      simpl in Hab. inversion Hab.
     }
   }
   {
   apply IHM'.
   }
 }
 { destruct ((b_eqb b0 (bid_of m))) eqn: Hb0. 
  {
    simpl. rewrite Hb0. lia. 
  }
  { simpl. rewrite Hb0. lia.
  }
 } Qed.

Lemma Remove_ab_trades_b_notIn (M:list transaction)(b:order)(a:order)
(NZT: forall m : transaction, In m M -> tquantity m > 0):
ttqb M b <= bq b -> ttq_ab M b a = bq b -> ~In b (bids_of (Remove_ab_trades M b a)).
Proof. intros. assert(ttqb M b = ttq_ab M b a + ttqb (Remove_ab_trades M b a) b). apply Remove_ab_trades_correct2b.
assert (ttqb (Remove_ab_trades M b a) b = 0). lia.
apply ttqb_intro in H2. auto. 
apply Remove_ab_trades_NZT. auto. Qed.

Lemma Remove_ab_trades_a_notIn (M:list transaction)(b:order)(a:order)
(NZT: forall m : transaction, In m M -> tquantity m > 0):
ttqa M a <= sq a -> ttq_ab M b a = sq a -> ~In a (asks_of (Remove_ab_trades M b a)).
Proof. intros. assert(ttqa M a = ttq_ab M b a + ttqa (Remove_ab_trades M b a) a). apply Remove_ab_trades_correct2a.
assert (ttqa (Remove_ab_trades M b a) a = 0). lia.
apply ttqa_intro in H2. auto. 
apply Remove_ab_trades_NZT. auto. Qed.


Lemma Remove_ab_trades_bids_subset (M:list transaction)(b:order)(a:order):
bids_of (Remove_ab_trades M b a) [<=] bids_of M.
Proof. induction M as [|m M']. simpl. auto.
simpl. destruct ((a_eqb a (ask_of m)) && (b_eqb b (bid_of m))) eqn:Hab.
eauto. simpl. eapply Subset_intro. auto. Qed.

Lemma Remove_ab_trades_asks_subset (M:list transaction)(b:order)(a:order):
asks_of (Remove_ab_trades M b a) [<=] asks_of M.
Proof. induction M as [|m M']. simpl. auto.
simpl. destruct ((a_eqb a (ask_of m)) && (b_eqb b (bid_of m))) eqn:Hab.
eauto. simpl. eapply Subset_intro. auto. Qed.

Lemma Remove_ab_trades_QM (M:list transaction)(b:order)(a:order):
QM (M) = QM (Remove_ab_trades M b a) + ttq_ab M b a.
Proof. induction M as [|m M']. simpl. auto.
simpl. destruct ((a_eqb a (ask_of m)) && (b_eqb b (bid_of m))) eqn:Hab.
simpl. lia. simpl. lia. Qed.

Lemma Remove_ab_trades_IR (M:list transaction)(b:order)(a:order):
Is_IR M-> Is_IR (Remove_ab_trades M b a).
Proof. unfold Is_IR. intros. assert(In m M \/ ~In m M).
eauto. destruct H1. auto. 
apply Remove_ab_trades_intro1 with (b:=b)(a:=a) in H1.
unfold not in H1. apply H1 in H0. elim H0.

Qed.

Lemma Remove_ab_trades_Uniform (M:list transaction)(b:order)(a:order):
Uniform M-> Uniform (Remove_ab_trades M b a).
Proof. induction M as [|m M'].
simpl. auto. unfold Uniform. simpl. 
intros. destruct ((a_eqb a (ask_of m)) && (b_eqb b (bid_of m))) eqn:Hab.
simpl in H. apply IHM'. unfold Uniform. 
apply uniform_elim2 with (a0:=tp m) in H. auto.
simpl. unfold Uniform in IHM'.
apply uniform_elim2 with (a0:=tp m) in H as H1.
apply IHM' in H1 as H2. 
cut((forall x, In x (trade_prices_of (Remove_ab_trades M' b a)) -> x=tp m)).
eapply uniform_intro. intros.
assert(In x (trade_prices_of M')).
assert(exists m0, (In m0 (Remove_ab_trades M' b a) /\ (x = tp m0))).
eauto.
destruct H3 as [m0 H3]. destruct H3.
assert(In m0 M').
eapply Remove_ab_trades_elim1 with(b:=b)(a:=a). auto.
subst x.
eauto.
assert(forall x, In x (trade_prices_of M') -> x=tp m).
eapply uniform_elim. auto. apply H4 in H3. 
auto.
Qed.

Lemma exists_M0_reduced_bid_ask_matching (M:list transaction) (B:list order)(A:list order)(b:order)(a:order)
(NZT:forall m : transaction, In m M -> tquantity m > 0):
matching_in (b::B) (a::A) M-> 
ttq_ab M b a = (bq b) /\ ((sq a) = (bq b)) ->
Is_IR M ->
(exists M0, (matching_in B A M0) /\Is_IR M0/\(QM(M)=QM(M0) + (bq b))/\
(forall m : transaction, In m M0 -> tquantity m > 0)).
Proof. intros H H0 IR. exists (Remove_ab_trades M b a).
split. 
  { split.
    split. 
    { apply Remove_ab_trades_matchable. apply H. }
      split.
      { intros. 
        assert(ttqb (Remove_ab_trades M b a) b0 <= ttqb M b0). 
        eapply Remove_ab_trades_ttq_le_b with (b0:=b0).
        assert(ttqb M b0 <= bq b0).  
        assert(In b0 (bids_of M) \/~In b0 (bids_of M)).
        eauto. destruct H3. 
        apply H. auto. apply ttqb_elim in H3. lia. lia.
      }
      { intros. 
        assert(ttqa (Remove_ab_trades M b a) a0 <= ttqa M a0). 
        eapply Remove_ab_trades_ttq_le_a with (a0:=a0).
        assert(ttqa M a0 <= sq a0).
        assert(In a0 (asks_of M) \/~In a0 (asks_of M)).
        eauto. destruct H3. 
        apply H. auto. apply ttqa_elim in H3. lia. lia.
      }
      { split. 
        { assert(bids_of (Remove_ab_trades M b a) [<=] bids_of M).
          apply Remove_ab_trades_bids_subset.
          assert(bids_of M [<=] (b::B)).
          apply H.
          assert(bids_of (Remove_ab_trades M b a) [<=] (b::B)).
          eauto. 
          assert(~In b (bids_of (Remove_ab_trades M b a))).
          apply Remove_ab_trades_b_notIn.
          auto. assert(In b (bids_of M) \/~In b (bids_of M)).
          eauto. destruct H4. 
          apply H. auto. apply ttqb_elim in H4. lia. 
          apply H0. eauto.
        }
        { assert(asks_of (Remove_ab_trades M b a) [<=] asks_of M).
          apply Remove_ab_trades_asks_subset.
          assert(asks_of M [<=] (a::A)).
          apply H.
          assert(asks_of (Remove_ab_trades M b a) [<=] (a::A)).
          eauto. 
          assert(~In a (asks_of (Remove_ab_trades M b a))).
          apply Remove_ab_trades_a_notIn.
          auto. assert(In a (asks_of M) \/~In a (asks_of M)).
          eauto. destruct H4. 
          apply H. auto. apply ttqa_elim in H4. lia. 
          destruct H0. lia. eauto.
        }
    }
  }
  { split.
  apply Remove_ab_trades_IR. apply IR.
  destruct H0. rewrite<- H0. split.
  apply Remove_ab_trades_QM. 
   apply Remove_ab_trades_NZT. auto.
 } Qed.




Theorem exists_M0_reduced_bid_ask_uniform (M:list transaction) (B:list order)(A:list order)(b:order)(a:order)
(NZT:forall m : transaction, In m M -> tquantity m > 0):
Is_uniform M (b::B) (a::A) -> ttq_ab M b a = (bq b) /\ ((sq a) = (bq b)) ->
(exists M0, (Is_uniform M0 B A) /\(QM(M)=QM(M0) + (bq b))/\
(forall m : transaction, In m M0 -> tquantity m > 0)).
Proof. intros. exists (Remove_ab_trades M b a).
split. 
{ split.
  { apply Remove_ab_trades_Uniform. apply H. }
  split. 
  { split. 
    { split. apply Remove_ab_trades_matchable. apply H.
      split.
      { intros. 
        assert(ttqb (Remove_ab_trades M b a) b0 <= ttqb M b0). 
        eapply Remove_ab_trades_ttq_le_b with (b0:=b0).
        assert(ttqb M b0 <= bq b0).  assert(In b0 (bids_of M) \/~In b0 (bids_of M)).
        eauto. destruct H3. 
        apply H. auto. apply ttqb_elim in H3. lia. lia.
      }
      { intros. 
        assert(ttqa (Remove_ab_trades M b a) a0 <= ttqa M a0). 
        eapply Remove_ab_trades_ttq_le_a with (a0:=a0).
        assert(ttqa M a0 <= sq a0).  assert(In a0 (asks_of M) \/~In a0 (asks_of M)).
        eauto. destruct H3. 
        apply H. auto. apply ttqa_elim in H3. lia. lia.
      }
    }
    { split. 
      { assert(bids_of (Remove_ab_trades M b a) [<=] bids_of M).
        apply Remove_ab_trades_bids_subset.
        assert(bids_of M [<=] (b::B)).
        apply H.
        assert(bids_of (Remove_ab_trades M b a) [<=] (b::B)).
        eauto. 
        assert(~In b (bids_of (Remove_ab_trades M b a))).
        apply Remove_ab_trades_b_notIn.
        auto. assert(In b (bids_of M) \/~In b (bids_of M)).
        eauto. destruct H4. 
        apply H. auto. apply ttqb_elim in H4. lia. 
        apply H0. eauto.
      }
      { assert(asks_of (Remove_ab_trades M b a) [<=] asks_of M).
        apply Remove_ab_trades_asks_subset.
        assert(asks_of M [<=] (a::A)).
        apply H.
        assert(asks_of (Remove_ab_trades M b a) [<=] (a::A)).
        eauto. 
        assert(~In a (asks_of (Remove_ab_trades M b a))).
        apply Remove_ab_trades_a_notIn.
        auto. assert(In a (asks_of M) \/~In a (asks_of M)).
        eauto. destruct H4. 
        apply H. auto. apply ttqa_elim in H4. lia. 
        destruct H0. lia. eauto.
      }
    }
  }
  {
  apply Remove_ab_trades_IR. apply H.
  }
 }
 split.
 { destruct H0. rewrite<- H0.
  apply Remove_ab_trades_QM.
 }
 {
 apply Remove_ab_trades_NZT. auto.
 } Qed.

(**************** case when the bid is partially traded *****************************)

Fixpoint replace_bid (M:list transaction)(b b':order):=
match M with 
|nil => nil
|m::M' =>match (b_eqb b (bid_of m)) with
  |true => (Mk_transaction b' (ask_of m) (tquantity m) (tp m))::replace_bid M' b b'
  |false =>m::replace_bid M' b b'
  end
end.

Lemma replace_bid_elim1 (M:list transaction)(b b':order) :
b=b' -> M = replace_bid M b b'.
Proof.  intros. induction M as [|m' M']. simpl. auto.
simpl. destruct (b_eqb b (bid_of m')) eqn: Hbm'.
simpl. f_equal. subst b'. move /eqP in Hbm'.
subst b. destruct m'. auto. auto. f_equal. auto. Qed.

Lemma replace_bid_elim2 (M:list transaction)(b b':order) :
b<>b' -> ~In b (bids_of (replace_bid M b b')).
Proof.  intros. induction M as [|m' M']. simpl. auto.
simpl. destruct (b_eqb b (bid_of m')) eqn: Hbm'.
simpl. eauto. simpl. intro. destruct H0. move /eqP in Hbm'.
subst b. elim Hbm'. auto. eauto. Qed.


Lemma replace_bid_subset_ask (M:list transaction)(b b':order):
asks_of M = asks_of (replace_bid M b b').
Proof.
revert b b'. induction M as [|m' M']. simpl. auto.
intros. simpl. destruct (b_eqb b (bid_of m')) eqn: Hbm'.
simpl. f_equal. apply IHM'.
simpl. f_equal. apply IHM'. Qed.

Lemma replace_bid_subset_prices (M:list transaction)(b b':order):
trade_prices_of M = trade_prices_of (replace_bid M b b').
Proof.
revert b b'. induction M as [|m' M']. simpl. auto.
intros. simpl. destruct (b_eqb b (bid_of m')) eqn: Hbm'.
simpl. f_equal. apply IHM'.
simpl. f_equal. apply IHM'. Qed.

Lemma replace_bid_subset_bids (M:list transaction)(b b':order)(B:list order):
bids_of M [<=] (b::B) -> bids_of (replace_bid M b b') [<=] (b'::B).
Proof.
revert b b' B. induction M as [|m' M']. simpl. auto.
intros. simpl. destruct (b_eqb b (bid_of m')) eqn: Hbm'.
simpl. simpl in H. assert(bids_of M' [<=] b :: B). 
eauto.  eapply IHM' with(b:=b)(b':=b') in H0.
unfold Subset. intros. destruct H1.
simpl. auto. eauto. simpl. simpl in H.
eapply Subset_elim1 in H as H1.
destruct H1. move /eqP in Hbm'. subst b.
elim Hbm'. auto.
eapply Subset_elim2 in H. eapply IHM' with (b:=b)(b':=b') in H.
unfold Subset.
intros. simpl. destruct H1. right. subst a. auto.
unfold Subset in H. apply H in H1.
destruct H1. left. auto. auto. Qed.

Lemma replace_bid_matchable (M:list transaction)(b b':order):
All_matchable M -> Nat.eqb (bp b) (bp b')-> All_matchable (replace_bid M b b').
Proof. induction M as [|m M']. simpl. auto.
unfold All_matchable.  
simpl. intros. 
destruct (b_eqb b (bid_of m)) eqn: Hm. 
{
  move /eqP in Hm. subst b.
  destruct H1. 
  { subst m0. simpl.
    specialize (H m). 
    destruct H. auto. move /eqP in H0. lia.
    move /eqP in H0. lia. 
  }
  eapply IHM' in H0.
  unfold All_matchable in H0. apply H0 in H1. auto.
  unfold All_matchable. intros. 
  specialize (H m1) as H3. 
  destruct H3. right. auto. auto. lia.
}
{
simpl in H1. destruct H1.
move /eqP in Hm. subst m. auto.
eapply IHM' in H0.  
apply H0 in H1. auto. 
unfold All_matchable. intros.
specialize (H m1) as H3.
destruct H3. auto. auto. lia.
} Qed. 


Lemma replace_bid_ttqb_b_b' (M:list transaction)(b b':order):
~In b' (bids_of M) -> ttqb M b =ttqb (replace_bid M b b') b'.
Proof. induction M as [|m M']. simpl. auto.
simpl. 
destruct (b_eqb b (bid_of m)) eqn: Hm. 
{ simpl. destruct (b_eqb b' b') eqn:Hbb'.
  intros. assert(~ In b' (bids_of M')).
  unfold not in H. auto. apply IHM' in H0. lia.
  move /eqP in Hbb'. elim Hbb'. auto.
}
{ simpl. destruct (b_eqb b' (bid_of m)) eqn:Hbm.
  intros. unfold not in H. 
  move /eqP in Hbm. symmetry in Hbm. 
  destruct H. auto. 
  intros. apply IHM'. auto.
}
Qed. 



Lemma replace_bid_ttqb_b0 (M:list transaction)(b b' b0:order):
b0<>b'/\b0<>b -> ttqb M b0 = ttqb (replace_bid M b b') b0.
Proof. induction M as [|m M']. simpl. auto.
simpl. 
destruct (b_eqb b0 (bid_of m)) eqn: Hm. 
{ simpl. destruct (b_eqb b (bid_of m)) eqn:Hbm.
  intros. destruct H. 
  move /eqP in Hbm. move /eqP in Hm. 
  subst. elim H0. auto. 
  intros. destruct H. simpl.
  rewrite Hm. rewrite IHM'.
  auto. lia. 
}
{ destruct (b_eqb b (bid_of m)) eqn:Hbm.
  intros. simpl. destruct H. 
  destruct (b_eqb b0 b') eqn:Hb.
  move /eqP in Hb. subst. elim H. auto. 
  apply IHM'. auto. simpl.
  rewrite Hm. auto. 
}
Qed.
 
Lemma replace_bid_ttqa (M:list transaction)(a:order)(b b':order):
ttqa M a = ttqa (replace_bid M b b') a.
Proof. induction M as [|m M']. simpl. auto.
simpl. 
destruct (a_eqb a (ask_of m)) eqn: Hm. 
{ destruct (b_eqb b (bid_of m)) eqn:Hbm.
  simpl. rewrite Hm. lia. 
  simpl.
  rewrite Hm. lia.
}
{ destruct (b_eqb b (bid_of m)) eqn:Hbm.
  simpl. rewrite Hm. lia. 
  simpl.
  rewrite Hm. lia.
}
Qed.

Lemma replace_bid_Uniform (M:list transaction)(b b':order):
Uniform M -> Uniform (replace_bid M b b').
Proof. unfold Uniform. 
assert(trade_prices_of M = trade_prices_of (replace_bid M b b')).
eapply replace_bid_subset_prices.
rewrite H. auto. Qed.


Lemma replace_bid_IR (M:list transaction)(b b':order):
Is_IR M -> b' >= b -> Is_IR (replace_bid M b b').
Proof. induction M as [|m M']. simpl. auto.
unfold Is_IR.  
simpl. intros. 
destruct (b_eqb b (bid_of m)) eqn: Hm. 
{
  move /eqP in Hm. subst b.
  destruct H1. 
  { subst m0. unfold rational.
    simpl.
    specialize (H m). 
    destruct H. auto. 
    lia.
  }
  eapply IHM' in H0.
  unfold Is_IR in H0. apply H0 in H1. auto.
  unfold Is_IR. intros. 
  specialize (H m1) as H3. 
  destruct H3. right. auto. auto.
}
{
simpl in H1. destruct H1.
move /eqP in Hm. subst m. auto.
eapply IHM' in H0.  
apply H0 in H1. auto. 
unfold Is_IR. intros.
specialize (H m1) as H3.
destruct H3. auto. auto. 
} Qed. 

Lemma replace_bid_QM (M:list transaction)(b b':order):
QM(M) = QM(replace_bid M b b').
Proof. induction M as [|m M']. simpl. auto.
simpl. destruct (b_eqb b (bid_of m)) eqn: Hm. simpl. lia.
simpl. lia. Qed.

Lemma replace_bid_NZT (M:list transaction)(b b':order)
(NZT:forall m : transaction, In m M -> tquantity m > 0):
(forall m : transaction, In m (replace_bid M b b') -> tquantity m > 0).
Proof. induction M as [|m M']. simpl. auto.
simpl. destruct (b_eqb b (bid_of m)) eqn: Hm. simpl.
intros. destruct H. subst m0. simpl. eauto.
apply IHM'. eauto. auto. 
simpl. intros. destruct H. subst m0.
apply NZT. eauto. apply IHM'.
eauto. auto. Qed.

Lemma replace_bid_matching1 (M:list transaction)(B:list order)(A:list order)(b b':order)
(NDB:NoDup (b'::B)):
matching_in (b::B) A M-> ttqb M b <= bq b' -> Nat.eqb (bp b) (bp b') ->
matching_in (b'::B) A (replace_bid M b b').
Proof. intros.  split.
{ split. 
  { apply replace_bid_matchable. apply H. auto. }
  { split. 
    { intros. destruct (b_eqb b b') eqn:Hbb'.
      { move /eqP in Hbb'. apply replace_bid_elim1 with (M:=M) in Hbb'.
        rewrite <- Hbb'. assert(In b0 (bids_of M)\/~In b0 (bids_of M)).
        eauto. destruct H3. apply H. auto.
        apply ttqb_elim in H3. lia.
      }
      { destruct (b_eqb b0 b') eqn:Hb0b';destruct (b_eqb b0 b) eqn:Hb0b.
        {
          move /eqP in Hb0b'. move /eqP in Hb0b.
          move /eqP in Hbb'. subst. elim Hbb'. auto.
        }
        {
          move /eqP in Hbb'. apply replace_bid_elim2 with (M:=M) in Hbb'.
          move /eqP in Hb0b'. subst. replace (ttqb (replace_bid M b b') b')
          with (ttqb M b). auto. apply replace_bid_ttqb_b_b'.
          assert((bids_of M)[<=](b::B)). apply H. intro.
          assert(In b' (b :: B)). eauto. destruct H5. 
          move /eqP in Hb0b. subst. elim Hb0b. auto.
          apply nodup_elim2 in NDB. eauto.
        }
        {
          move /eqP in Hbb'. apply replace_bid_elim2 with (M:=M) in Hbb'.
          move /eqP in Hb0b. subst. unfold not in Hbb'. 
          apply Hbb' in H2. elim H2.
        }
        {
          move /eqP in Hb0b'. move /eqP in Hb0b.
          move /eqP in Hbb'. replace (ttqb (replace_bid M b b') b0) 
          with (ttqb M b0). assert(In b0 (bids_of M)\/~In b0 (bids_of M)).
          eauto. destruct H3. apply H. auto.
          apply ttqb_elim in H3. lia.
          eapply replace_bid_ttqb_b0. auto.
         }
       }
    }
    {
    intros. replace (ttqa (replace_bid M b b') a) with (ttqa M a).
    assert(In a (asks_of M)\/~In a (asks_of M)).
    eauto. destruct H3. apply H. auto.
    apply ttqa_elim in H3. lia. apply replace_bid_ttqa.
    }
  }
}
{
  split.
  { apply replace_bid_subset_bids. apply H. }
  { rewrite <- replace_bid_subset_ask. apply H. }
} Qed.

Lemma exists_M0_reduced_bid_uniform (M:list transaction)(B:list order)(A:list order)(b:order)(a:order)
(NDB:NoDup (idbs_of (b::B)))
(NZT:forall m : transaction, In m M -> tquantity m > 0):
Is_uniform M (b::B) (a::A) -> 
ttq_ab M b a = (sq a) ->
((bq b) > (sq a)) -> 
exists M0, (Is_uniform M0 ((Mk_bid (bp b) (btime b) (bq b - (sq a)) (idb b))::B)
A)
/\(QM(M)=QM(M0) + (sq a)/\
(forall m : transaction, In m M0 -> tquantity m > 0)).
Proof. intros. 
set (b':={| bp := b; btime := btime b; bq := bq b - sq a; idb := idb b |}).
exists (replace_bid (Remove_ab_trades M b a) b b').
split. 
  { split.
    { apply replace_bid_Uniform. apply Remove_ab_trades_Uniform. apply H. }
    split. 
    { apply replace_bid_matching1. apply idbs_of_nodup. simpl.
      simpl in NDB. auto.
      { split. (*Proof that matching *)
        split.
        apply Remove_ab_trades_matchable. apply H.
        split. 
        { intros. assert(ttqb (Remove_ab_trades M b a) b0 <= ttqb M b0).
          apply Remove_ab_trades_ttq_le_b.
          assert(ttqb M b0 <= bq b0). 
          assert(In b0 (bids_of M)\/~In b0 (bids_of M)).
          eauto. destruct H4. apply H. auto.
          apply ttqb_elim in H4. lia. lia.
        }
        { intros. assert(ttqa (Remove_ab_trades M b a) a0 <= ttqa M a0).
          apply Remove_ab_trades_ttq_le_a.
          assert(ttqa M a0 <= sq a0). 
          assert(In a0 (asks_of M)\/~In a0 (asks_of M)).
          eauto. destruct H4. apply H. auto.
          apply ttqa_elim in H4. lia. lia.
        }
        split. assert(bids_of (Remove_ab_trades M b a) [<=] bids_of M).
        apply Remove_ab_trades_bids_subset.
        assert(bids_of M [<=] (b::B)). apply H.
        eauto.
        assert(asks_of (Remove_ab_trades M b a) [<=] asks_of M).
        apply Remove_ab_trades_asks_subset.
        assert(asks_of M [<=] (a::A)).  apply H.
        assert(~In a (asks_of (Remove_ab_trades M b a))).
        apply Remove_ab_trades_a_notIn. auto. 
        assert(In a (asks_of M)\/~In a (asks_of M)).
        eauto. destruct H4. apply H. auto.
        apply ttqa_elim in H4. lia. lia.
        assert(asks_of (Remove_ab_trades M b a) [<=] (a::A)).
        eauto. eauto.
      }        
      subst b'. 
      simpl. assert (ttqb M b = (ttq_ab M b a) + (ttqb (Remove_ab_trades M b a) b)).
      apply Remove_ab_trades_correct2b. 
      assert(In b (bids_of M)\/~In b (bids_of M)).
      eauto. destruct H3.
      assert(ttqb M b <= bq b). apply H. auto. lia.
       apply ttqb_elim in H3. lia. subst b'. simpl. auto. 
    }
    { apply replace_bid_IR. apply Remove_ab_trades_IR. apply H.
      subst b'. simpl. auto.
    }
  }
  split.
{ 
  replace (QM (replace_bid (Remove_ab_trades M b a) b b')) with 
  (QM (Remove_ab_trades M b a)). 
  assert(QM M = QM (Remove_ab_trades M b a) + ttq_ab M b a). 
  apply Remove_ab_trades_QM. lia.
  apply replace_bid_QM.
}
{
apply replace_bid_NZT.
apply Remove_ab_trades_NZT.
auto.
} Qed.
   

Lemma exists_M0_reduced_bid_matching (M:list transaction)(B:list order)(A:list order)(b:order)(a:order)
(NDB:NoDup (idbs_of (b::B)))
(NZT:forall m : transaction, In m M -> tquantity m > 0):
matching_in (b::B) (a::A) M-> 
ttq_ab M b a = (sq a) ->
((bq b) > (sq a)) -> 
Is_IR M ->
exists M0, (matching_in ((Mk_bid (bp b) (btime b) (bq b - (sq a)) (idb b))::B)
A M0)
/\(QM(M)=QM(M0) + (sq a)/\Is_IR M0 /\
(forall m : transaction, In m M0 -> tquantity m > 0)).
Proof. intros. 
set (b':={| bp := b; btime := btime b; bq := bq b - sq a; idb := idb b |}).
exists (replace_bid (Remove_ab_trades M b a) b b').
split. { apply replace_bid_matching1. apply idbs_of_nodup. simpl.
      simpl in NDB. auto.
      { split. (*Proof that matching *)
        split.
        apply Remove_ab_trades_matchable. apply H.
        split. 
        { intros. assert(ttqb (Remove_ab_trades M b a) b0 <= ttqb M b0).
          apply Remove_ab_trades_ttq_le_b.
          assert(ttqb M b0 <= bq b0). 
          assert(In b0 (bids_of M)\/~In b0 (bids_of M)).
          eauto. destruct H5. apply H. auto.
          apply ttqb_elim in H5. lia. lia.
        }
        { intros. assert(ttqa (Remove_ab_trades M b a) a0 <= ttqa M a0).
          apply Remove_ab_trades_ttq_le_a.
          assert(ttqa M a0 <= sq a0). 
          assert(In a0 (asks_of M)\/~In a0 (asks_of M)).
          eauto. destruct H5. apply H. auto.
          apply ttqa_elim in H5. lia. lia.
        }
        split. assert(bids_of (Remove_ab_trades M b a) [<=] bids_of M).
        apply Remove_ab_trades_bids_subset.
        assert(bids_of M [<=] (b::B)). apply H.
        eauto.
        assert(asks_of (Remove_ab_trades M b a) [<=] asks_of M).
        apply Remove_ab_trades_asks_subset.
        assert(asks_of M [<=] (a::A)).  apply H.
        assert(~In a (asks_of (Remove_ab_trades M b a))).
        apply Remove_ab_trades_a_notIn. auto. 
        assert(In a (asks_of M)\/~In a (asks_of M)).
        eauto. destruct H5. apply H. auto.
        apply ttqa_elim in H5. lia. lia.
        assert(asks_of (Remove_ab_trades M b a) [<=] (a::A)).
        eauto. eauto.
      }        
      subst b'. 
      simpl. assert (ttqb M b = (ttq_ab M b a) + (ttqb (Remove_ab_trades M b a) b)).
      apply Remove_ab_trades_correct2b. 
      assert(In b (bids_of M)\/~In b (bids_of M)).
      eauto. destruct H4.
      assert(ttqb M b <= bq b). apply H. auto. lia.
       apply ttqb_elim in H4. lia. subst b'. simpl. auto. 
    }
    split.
    { 
     replace (QM (replace_bid (Remove_ab_trades M b a) b b')) with 
     (QM (Remove_ab_trades M b a)). 
     assert(QM M = QM (Remove_ab_trades M b a) + ttq_ab M b a). 
     apply Remove_ab_trades_QM. lia.
     apply replace_bid_QM.
   }
   split.
   { apply replace_bid_IR. apply Remove_ab_trades_IR. apply H2.
      subst b'. simpl. auto.
   }
   apply replace_bid_NZT.
apply Remove_ab_trades_NZT.
auto.
Qed.









(**************** case when the ask is partially traded *****************************)




Fixpoint replace_ask  (M:list transaction)(a a':order):=
match M with 
|nil => nil
|m::M' =>match (a_eqb a (ask_of m)) with
  |true => (Mk_transaction (bid_of m) a' (tquantity m) (tp m))::replace_ask M' a a'
  |false =>m::replace_ask M' a a'
  end
end.

Lemma replace_ask_elim1 (M:list transaction)(a a':order) :
a=a' -> M = replace_ask M a a'.
Proof.  intros. induction M as [|m' M']. simpl. auto.
simpl. destruct (a_eqb a (ask_of m')) eqn: Hbm'.
simpl. f_equal. subst a'. move /eqP in Hbm'.
subst a. destruct m'. auto. auto. f_equal. auto. Qed.

Lemma replace_ask_elim2 (M:list transaction)(a a':order) :
a<>a' -> ~In a (asks_of (replace_ask M a a')).
Proof.  intros. induction M as [|m' M']. simpl. auto.
simpl. destruct (a_eqb a (ask_of m')) eqn: Hbm'.
simpl. eauto. simpl. intro. destruct H0. move /eqP in Hbm'.
subst a. elim Hbm'. auto. eauto. Qed.


Lemma replace_ask_subset_bid (M:list transaction)(a a':order):
bids_of M = bids_of (replace_ask M a a').
Proof.
revert a a'. induction M as [|m' M']. simpl. auto.
intros. simpl. destruct (a_eqb a (ask_of m')) eqn: Hbm'.
simpl. f_equal. apply IHM'.
simpl. f_equal. apply IHM'. Qed.

Lemma replace_ask_subset_prices (M:list transaction)(a a':order):
trade_prices_of M = trade_prices_of (replace_ask M a a').
Proof.
revert a a'. induction M as [|m' M']. simpl. auto.
intros. simpl. destruct (a_eqb a (ask_of m')) eqn: Hbm'.
simpl. f_equal. apply IHM'.
simpl. f_equal. apply IHM'. Qed.

Lemma replace_ask_subset_asks (M:list transaction)(a a':order)(A:list order):
asks_of M [<=] (a::A) -> asks_of (replace_ask M a a') [<=] (a'::A).
Proof.
revert a a' A. induction M as [|m' M']. simpl. auto.
intros. simpl. destruct (a_eqb a (ask_of m')) eqn: Hbm'.
simpl. simpl in H. assert(asks_of M' [<=] a :: A). 
eauto.  eapply IHM' with(a:=a)(a':=a') in H0.
unfold Subset. intros. destruct H1.
simpl. auto. eauto. simpl. simpl in H.
eapply Subset_elim1 in H as H1.
destruct H1. move /eqP in Hbm'. subst a.
elim Hbm'. auto.
eapply Subset_elim2 in H. eapply IHM' with (a:=a)(a':=a') in H.
unfold Subset.
intros. simpl. destruct H1. right. subst a0. auto.
unfold Subset in H. apply H in H1.
destruct H1. left. auto. auto. Qed.

Lemma replace_ask_matchable (M:list transaction)(a a':order):
All_matchable M -> Nat.eqb (sp a) (sp a')-> All_matchable (replace_ask M a a').
Proof. induction M as [|m M']. simpl. auto.
unfold All_matchable.  
simpl. intros. 
destruct (a_eqb a (ask_of m)) eqn: Hm. 
{
  move /eqP in Hm. subst a.
  destruct H1. 
  { subst m0. simpl.
    specialize (H m). 
    destruct H. auto. move /eqP in H0. lia.
    move /eqP in H0. lia. 
  }
  eapply IHM' in H0.
  unfold All_matchable in H0. apply H0 in H1. auto.
  unfold All_matchable. intros. 
  specialize (H m1) as H3. 
  destruct H3. right. auto. auto. lia.
}
{
simpl in H1. destruct H1.
move /eqP in Hm. subst m. auto.
eapply IHM' in H0.  
apply H0 in H1. auto. 
unfold All_matchable. intros.
specialize (H m1) as H3.
destruct H3. auto. auto. lia.
} Qed. 


Lemma replace_ask_ttqa_a_a' (M:list transaction)(a a':order):
~In a' (asks_of M) -> ttqa M a =ttqa (replace_ask M a a') a'.
Proof. induction M as [|m M']. simpl. auto.
simpl. 
destruct (a_eqb a (ask_of m)) eqn: Hm. 
{ simpl. destruct (a_eqb a' a') eqn:Hbb'.
  intros. assert(~ In a' (asks_of M')).
  unfold not in H. auto. apply IHM' in H0. lia.
  move /eqP in Hbb'. elim Hbb'. auto.
}
{ simpl. destruct (a_eqb a' (ask_of m)) eqn:Hbm.
  intros. unfold not in H. 
  move /eqP in Hbm. symmetry in Hbm. 
  destruct H. auto. 
  intros. apply IHM'. auto.
}
Qed. 



Lemma replace_ask_ttqa_a0 (M:list transaction)(a a' a0:order):
a0<>a'/\a0<>a -> ttqa M a0 = ttqa (replace_ask M a a') a0.
Proof. induction M as [|m M']. simpl. auto.
simpl. 
destruct (a_eqb a0 (ask_of m)) eqn: Hm. 
{ simpl. destruct (a_eqb a (ask_of m)) eqn:Hbm.
  intros. destruct H. 
  move /eqP in Hbm. move /eqP in Hm. 
  subst. elim H0. auto. 
  intros. destruct H. simpl.
  rewrite Hm. rewrite IHM'.
  auto. lia. 
}
{ destruct (a_eqb a (ask_of m)) eqn:Hbm.
  intros. simpl. destruct H. 
  destruct (a_eqb a0 a') eqn:Hb.
  move /eqP in Hb. subst. elim H. auto. 
  apply IHM'. auto. simpl.
  rewrite Hm. auto. 
}
Qed.
 
Lemma replace_ask_ttqb (M:list transaction)(b:order)(a a':order):
ttqb M b = ttqb (replace_ask M a a') b.
Proof. induction M as [|m M']. simpl. auto.
simpl. 
destruct (b_eqb b (bid_of m)) eqn: Hm. 
{ destruct (a_eqb a (ask_of m)) eqn:Hbm.
  simpl. rewrite Hm. lia. 
  simpl.
  rewrite Hm. lia.
}
{ destruct (a_eqb a (ask_of m)) eqn:Hbm.
  simpl. rewrite Hm. lia. 
  simpl.
  rewrite Hm. lia.
}
Qed.

Lemma replace_ask_Uniform (M:list transaction)(a a':order):
Uniform M -> Uniform (replace_ask M a a').
Proof. unfold Uniform. 
assert(trade_prices_of M = trade_prices_of (replace_ask M a a')).
eapply replace_ask_subset_prices.
rewrite H. auto. Qed.


Lemma replace_ask_IR (M:list transaction)(a a':order):
Is_IR M -> a' <= a -> Is_IR (replace_ask M a a').
Proof. induction M as [|m M']. simpl. auto.
unfold Is_IR.  
simpl. intros. 
destruct (a_eqb a (ask_of m)) eqn: Hm. 
{
  move /eqP in Hm. subst a.
  destruct H1. 
  { subst m0. unfold rational.
    simpl.
    specialize (H m). 
    destruct H. auto. 
    lia.
  }
  eapply IHM' in H0.
  unfold Is_IR in H0. apply H0 in H1. auto.
  unfold Is_IR. intros. 
  specialize (H m1) as H3. 
  destruct H3. right. auto. auto.
}
{
simpl in H1. destruct H1.
move /eqP in Hm. subst m. auto.
eapply IHM' in H0.  
apply H0 in H1. auto. 
unfold Is_IR. intros.
specialize (H m1) as H3.
destruct H3. auto. auto. 
} Qed. 

Lemma replace_ask_QM (M:list transaction)(a a':order):
QM(M) = QM(replace_ask M a a').
Proof. induction M as [|m M']. simpl. auto.
simpl. destruct (a_eqb a (ask_of m)) eqn: Hm. simpl. lia.
simpl. lia. Qed.

Lemma replace_ask_NZT (M:list transaction)(a a':order)
(NZT:forall m : transaction, In m M -> tquantity m > 0):
(forall m : transaction, In m (replace_ask M a a') -> tquantity m > 0).
Proof. induction M as [|m M']. simpl. auto.
simpl. destruct (a_eqb a (ask_of m)) eqn: Hm. simpl.
intros. destruct H. subst m0. simpl. eauto.
apply IHM'. eauto. auto. 
simpl. intros. destruct H. subst m0.
apply NZT. eauto. apply IHM'.
eauto. auto. Qed.

Lemma replace_ask_matching1 (M:list transaction)(B:list order)(A:list order)(a a':order)
(NDA:NoDup (a'::A)):
matching_in B (a::A) M-> ttqa M a <= sq a' -> Nat.eqb (sp a) (sp a') ->
matching_in B (a'::A) (replace_ask M a a').
Proof. intros.  split.
{ split. 
  { apply replace_ask_matchable. apply H. auto. }
  { split. 
    {
    intros. replace (ttqb (replace_ask M a a') b) with (ttqb M b).
    assert(In b (bids_of M)\/~In b (bids_of M)).
    eauto. destruct H3. apply H. auto.
    apply ttqb_elim in H3. lia. apply replace_ask_ttqb.
    }
    { intros. destruct (a_eqb a a') eqn:Hbb'.
      { move /eqP in Hbb'. apply replace_ask_elim1 with (M:=M) in Hbb'.
        rewrite <- Hbb'. assert(In a0 (asks_of M)\/~In a0 (asks_of M)).
        eauto. destruct H3. apply H. auto.
        apply ttqa_elim in H3. lia.
      }
      { destruct (a_eqb a0 a') eqn:Hb0b';destruct (a_eqb a0 a) eqn:Hb0b.
        {
          move /eqP in Hb0b'. move /eqP in Hb0b.
          move /eqP in Hbb'. subst. elim Hbb'. auto.
        }
        {
          move /eqP in Hbb'. apply replace_ask_elim2 with (M:=M) in Hbb'.
          move /eqP in Hb0b'. subst. replace (ttqa (replace_ask M a a') a')
          with (ttqa M a). auto. apply replace_ask_ttqa_a_a'.
          assert((asks_of M)[<=](a::A)). apply H. intro.
          assert(In a' (a :: A)). eauto. destruct H5. 
          move /eqP in Hb0b. subst. elim Hb0b. auto.
          apply nodup_elim2 in NDA. eauto.
        }
        {
          move /eqP in Hbb'. apply replace_ask_elim2 with (M:=M) in Hbb'.
          move /eqP in Hb0b. subst. unfold not in Hbb'. 
          apply Hbb' in H2. elim H2.
        }
        {
          move /eqP in Hb0b'. move /eqP in Hb0b.
          move /eqP in Hbb'. replace (ttqa (replace_ask M a a') a0) 
          with (ttqa M a0). assert(In a0 (asks_of M)\/~In a0 (asks_of M)).
          eauto. destruct H3. apply H. auto.
          apply ttqa_elim in H3. lia.
          eapply replace_ask_ttqa_a0. auto.
         }
       }
    }
  }
}
{
  split.
  { rewrite <- replace_ask_subset_bid. apply H. }
  { apply replace_ask_subset_asks. apply H. }

} Qed.


Lemma exists_M0_reduced_ask_matching (M:list transaction)(B:list order)(A:list order)(b:order)(a:order)
(NDA:NoDup (idas_of (a::A)))
(NZT:forall m : transaction, In m M -> tquantity m > 0):
matching_in (b::B) (a::A) M-> 
ttq_ab M b a = (bq b) ->
((sq a) > (bq b)) -> 
Is_IR M ->
exists M0, (matching_in B
((Mk_ask (sp a) (stime a) (sq a - (bq b)) (ida a))::A) M0)
/\(QM(M)=QM(M0) + (bq b)/\Is_IR M0/\
(forall m : transaction, In m M0 -> tquantity m > 0)).
Proof. intros. 
set (a':={| sp := a; stime := stime a; sq := sq a - bq b; ida := ida a |}).
exists (replace_ask (Remove_ab_trades M b a) a a').
split. { apply replace_ask_matching1. apply idas_of_nodup. simpl.
      simpl in NDA. auto.
      { split. (*Proof that matching *)
        split.
        apply Remove_ab_trades_matchable. apply H.
        split. 
        { intros. assert(ttqb (Remove_ab_trades M b a) b0 <= ttqb M b0).
          apply Remove_ab_trades_ttq_le_b.
          assert(ttqb M b0 <= bq b0). 
          assert(In b0 (bids_of M)\/~In b0 (bids_of M)).
          eauto. destruct H5. apply H. auto.
          apply ttqb_elim in H5. lia. lia.
        }
        { intros. assert(ttqa (Remove_ab_trades M b a) a0 <= ttqa M a0).
          apply Remove_ab_trades_ttq_le_a.
          assert(ttqa M a0 <= sq a0). 
          assert(In a0 (asks_of M)\/~In a0 (asks_of M)).
          eauto. destruct H5. apply H. auto.
          apply ttqa_elim in H5. lia. lia.
        }
        split. 
        { assert(bids_of (Remove_ab_trades M b a) [<=] bids_of M).
          apply Remove_ab_trades_bids_subset.
          assert(bids_of M [<=] (b::B)).  apply H.
          assert(~In b (bids_of (Remove_ab_trades M b a))).
          apply Remove_ab_trades_b_notIn. auto. 
          assert(In b (bids_of M)\/~In b (bids_of M)).
          eauto. destruct H5. apply H. auto.
          apply ttqb_elim in H5. lia. lia.
          assert(bids_of (Remove_ab_trades M b a) [<=] (b::B)).
          eauto. eauto.
        }
        { assert(asks_of (Remove_ab_trades M b a) [<=] asks_of M).
          apply Remove_ab_trades_asks_subset.
          assert(asks_of M [<=] (a::A)). apply H.
          eauto.
        }        
      }        
      subst a'. 
      simpl. assert (ttqa M a = (ttq_ab M b a) + (ttqa (Remove_ab_trades M b a) a)).
      apply Remove_ab_trades_correct2a. 
      assert(In a (asks_of M)\/~In a (asks_of M)).
      eauto. destruct H4.
      assert(ttqa M a <= sq a). apply H. auto. lia.
       apply ttqa_elim in H4. lia. subst a'. simpl. auto. 
    }
    split.
    { 
     replace (QM (replace_ask (Remove_ab_trades M b a) a a')) with 
     (QM (Remove_ab_trades M b a)). 
     assert(QM M = QM (Remove_ab_trades M b a) + ttq_ab M b a). 
     apply Remove_ab_trades_QM. lia.
     apply replace_ask_QM.
   }
   split.
   { apply replace_ask_IR. apply Remove_ab_trades_IR. apply H2.
      subst a'. simpl. auto.
   }
   apply replace_ask_NZT.
apply Remove_ab_trades_NZT.
auto.
Qed.





Lemma exists_M0_reduced_ask_uniform (M:list transaction)(B:list order)(A:list order)(b:order)(a:order)
(NDA:NoDup (idas_of (a::A)))
(NZT:forall m : transaction, In m M -> tquantity m > 0):
Is_uniform M (b::B) (a::A) -> 
ttq_ab M b a = (bq b) ->
((sq a) > (bq b)) -> 
exists M0, (Is_uniform M0 B
((Mk_ask (sp a) (stime a) (sq a - (bq b)) (ida a))::A))
/\(QM(M)=QM(M0) + (bq b)/\
(forall m : transaction, In m M0 -> tquantity m > 0)).
Proof. intros. 
set (a':={| sp := a; stime := stime a; sq := sq a - bq b; ida := ida a |}).
exists (replace_ask (Remove_ab_trades M b a) a a').
split. 
  { split.
    { apply replace_ask_Uniform. apply Remove_ab_trades_Uniform. apply H. }
    split. 
{ apply replace_ask_matching1. apply idas_of_nodup. simpl.
      simpl in NDA. auto.
      { split. (*Proof that matching *)
        split.
        apply Remove_ab_trades_matchable. apply H.
        split. 
        { intros. assert(ttqb (Remove_ab_trades M b a) b0 <= ttqb M b0).
          apply Remove_ab_trades_ttq_le_b.
          assert(ttqb M b0 <= bq b0). 
          assert(In b0 (bids_of M)\/~In b0 (bids_of M)).
          eauto. destruct H4. apply H. auto.
          apply ttqb_elim in H4. lia. lia.
        }
        { intros. assert(ttqa (Remove_ab_trades M b a) a0 <= ttqa M a0).
          apply Remove_ab_trades_ttq_le_a.
          assert(ttqa M a0 <= sq a0). 
          assert(In a0 (asks_of M)\/~In a0 (asks_of M)).
          eauto. destruct H4. apply H. auto.
          apply ttqa_elim in H4. lia. lia.
        }
        split. 
        { assert(bids_of (Remove_ab_trades M b a) [<=] bids_of M).
          apply Remove_ab_trades_bids_subset.
          assert(bids_of M [<=] (b::B)).  apply H.
          assert(~In b (bids_of (Remove_ab_trades M b a))).
          apply Remove_ab_trades_b_notIn. auto. 
          assert(In b (bids_of M)\/~In b (bids_of M)).
          eauto. destruct H4. apply H. auto.
          apply ttqb_elim in H4. lia. lia.
          assert(bids_of (Remove_ab_trades M b a) [<=] (b::B)).
          eauto. eauto.
        }
        { assert(asks_of (Remove_ab_trades M b a) [<=] asks_of M).
          apply Remove_ab_trades_asks_subset.
          assert(asks_of M [<=] (a::A)). apply H.
          eauto.
        }
      }
      subst a'. 
      simpl. assert (ttqa M a = (ttq_ab M b a) + (ttqa (Remove_ab_trades M b a) a)).
      apply Remove_ab_trades_correct2a. 
      assert(In a (asks_of M)\/~In a (asks_of M)).
      eauto. destruct H3.
      assert(ttqa M a <= sq a). apply H. auto. lia.
      apply ttqa_elim in H3. lia. subst a'. simpl. auto. 
    }
   { apply replace_ask_IR. apply Remove_ab_trades_IR. apply H.
      subst a'. simpl. auto.
   }
   }
   split.
    { 
     replace (QM (replace_ask (Remove_ab_trades M b a) a a')) with 
     (QM (Remove_ab_trades M b a)). 
     assert(QM M = QM (Remove_ab_trades M b a) + ttq_ab M b a). 
     apply Remove_ab_trades_QM. lia.
     apply replace_ask_QM.
   }
   apply replace_ask_NZT.
   apply Remove_ab_trades_NZT.
   auto.
Qed.

End Transform.
*)