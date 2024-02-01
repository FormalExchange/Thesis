Require Export Fair_Bid.

Definition FOA M A:= let A:= (Incr_Ask.sort A) in
                     let M:= (Incr_M.sort M) in
                     FOA_aux M A.

Definition FOB M B:= let B:= (Decr_Bid.sort B) in
                     let M:= (Decr_M.sort M) in
                     FOB_aux M B.

Lemma FOA_correct M B A:
admissible B A /\ Matching M B A ->
Matching (FOA M A) B A /\                                                       (* (a) *)
Vol(M) = Vol(FOA M A) /\                                                        (* (b) *)
Is_fair_asks (FOA M A) A /\                                                     (* (c) *)
(forall b, In b B -> Qty_bid M (id(b)) = Qty_bid (FOA M A) (id(b)))/\           (* (d) *)
(Is_fair_bids M B -> Is_fair_bids (FOA M A) B).
Proof. intros. apply FOA_aux_correct in H. unfold FOA. Admitted.

Lemma FOB_correct M B A:
admissible B A /\ Matching M B A ->
Matching (FOB M B) B A /\                                                       (* (a) *)
Vol(M) = Vol(FOB M B) /\                                                        (* (b) *)
Is_fair_bids (FOB M B) A /\                                                     (* (c) *)
(forall a, In a A -> Qty_ask M (id(a)) = Qty_ask (FOB M B) (id(a)))/\           (* (d) *)
(Is_fair_asks M A -> Is_fair_asks (FOB M B) A).
Proof. intros. apply FOB_aux_correct in H. unfold FOB. Admitted.


Definition Fair M B A := FOA (FOB M B) A.

Theorem Fair_main (M: list transaction) (B A: list order):
        admissible B A /\ Matching M B A ->
        (Matching (Fair M B A) B A) /\ (* (Fair M B A) is a matching over (B, A) *)
        (Vol(M)= Vol((Fair M B A))) /\ (* Trade volumes of M and (Fair M B A) are the same *)
        (Is_fair (Fair M B A) B A). (* Process Fair produces a fair matching *)
Proof. unfold Fair. unfold FOA. unfold FOB. intro. Search "_perm".
       apply FOA_correct in H as H1. apply FOB_correct in H as H2. destruct H1.
       destruct H1. destruct H3. destruct H4. destruct H2. destruct H6. destruct H7. destruct H8.
       split. apply H0. 
