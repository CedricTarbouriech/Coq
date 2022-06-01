Require Import Setoid.
Require Import Classical.

(***********
 *         *
 * Bennett *
 *         *
 ***********)
Parameter Entity: Set.
Parameter F : Entity -> Entity -> Prop.
Parameter Ps : Entity -> Entity -> Prop.
Definition P x y := exists s, F x s /\ Ps s y.
Definition PP x y := P x y /\ ~ P y x.
Definition O x y := exists z, P z x /\ P z y.
Definition Os x y := exists z, Ps z x /\ Ps z y.
Definition PPs x y := Ps x y /\ ~ F y x.

(* Only Slots are Filled *)
Axiom only_slots_are_filled : forall x y,
  F x y -> exists z, Ps y z.

(* Slots Cannot Fill *)
Axiom slots_cannot_fill : forall x y,
  F x y -> ~exists z, Ps x z.

(* Slots Don’t Have Slots *)
Axiom slots_dont_have_slots : forall x y,
  Ps x y -> ~exists z, Ps z x.

(* Filler Irreflexivity *)
Theorem BT1 : forall x,
  ~ F x x.
Proof.
  intros x h.
  apply only_slots_are_filled in h as h1.
  apply slots_cannot_fill in h as h2.
  contradiction.
Qed.

(* Filler Asymmetry *)
Theorem BT2 : forall x y,
  F x y -> ~ F y x.
Proof.
  intros x y H.
  apply only_slots_are_filled in H.
  intro h.
  apply slots_cannot_fill in h.
  contradiction.
Qed.

(* Filler Transitivity *)
Theorem BT3 : forall x y z,
  (F x y /\ F y z) -> F x z.
Proof.
  intros x y z [].
  apply only_slots_are_filled in H as [].
  apply slots_cannot_fill in H0 as [].
  exists x0.
  apply H.
Qed.

(* Slot Irreflexivity *)
Theorem BT4 : forall x,
  ~Ps x x.
Proof.
  intros x h.
  apply slots_dont_have_slots in h as h1.
  destruct h1.
  exists x.
  assumption.
Qed.

(* Slot Asymmetry *)
Theorem BT5 : forall x y,
  Ps x y -> ~ Ps y x.
Proof.
  intros x y H h.
  apply slots_dont_have_slots in h as [].
  exists x.
  assumption.
Qed.

(* Slot Transitivity *)
Theorem BT6 : forall x y z,
  (Ps x y /\ Ps y z) -> Ps x z.
Proof.
  intros x y z [].
  apply slots_dont_have_slots in H0 as [].
  exists x.
  assumption.
Qed.

(* Improper Parthood Slots *)
Axiom whole_improper_slots : forall x,
  (exists y, Ps y x) -> (exists z, Ps z x /\ F x z).

(* Slot Inheritance *)
Axiom slot_inheritance : forall x y z1 z2,
  (Ps z1 y /\ F x z1) /\ Ps z2 x -> Ps z2 y.

(* Mutual Occupancy is Identity *)
Axiom mutual_occupancy : forall x y z1 z2,
  (Ps z1 y /\ F x z1) /\ (Ps z2 x /\ F y z2) -> x = y.

(* Single Occupancy *)
Axiom single_occupancy : forall x y,
  Ps x y -> exists! z, F z x.

(* Parthood Transitivity *)
Theorem parthood_transitivity : forall x y z,
  (P x y /\ P y z) -> P x z.
Proof.
  firstorder.
  unfold P.
  eauto 6 using slot_inheritance.
Qed.

(* Anti-Symmetry *)
Theorem BT8 : forall x y,
  (P x y /\ P y x) -> x = y.
Proof.
  unfold P.
  firstorder.
  apply mutual_occupancy with (z1 := x1) (z2 := x0).
  auto.
Qed.

(* Conditional Reflexivity *)
Theorem BT9 : forall x,
  (exists z, Ps z x) -> P x x.
Proof.
  intros x h.
  apply whole_improper_slots in h as [y ].
  unfold P.
  exists y.
  apply and_comm; assumption.
Qed.

(* Parts <-> Slots *)
Theorem BT11 : forall y,
  ((exists x, P x y) <-> (exists z, Ps z y)).
Proof.
  intro y.
  unfold P.
  split.
  - intros [x [s []]].
    exists s.
    assumption.
  - intros [z Pszy].
    apply single_occupancy in Pszy as H1.
    destruct H1 as [x []].
    exists x, z.
    split; assumption.
Qed.

(* Composites <-> Slot-Composites *)
Theorem BT12 : forall y,
  ((exists x, PP x y) <-> (exists z, PPs z y)).
Proof.
  unfold PP, PPs, P.
  intro b.
  split.
  (* left to right *)
  - intros [a [[c [Fac Pscb]] nPba]].
    exists c.
    split.
    -- apply Pscb.
    -- pose proof (single_occupancy _ _ Pscb) as [d [Fdc Uc]].
       intros Fbc.
       pose proof (Uc a Fac). subst.
       pose proof (Uc b Fbc). subst.
       apply nPba.
       exists c; split.
       apply Fbc.
       apply Pscb.
  (* right to left *)
  - intros [a [Psab nFba]].
    pose proof (single_occupancy _ _ Psab) as [c [Fca Uc]].
    exists c.
    split.
    + exists a; split; eauto.
    + intros [d [Fbd Psfc]].
    apply nFba.
    assert (b = c) as Heqbc.
    * eapply mutual_occupancy with (z1 := d) (z2 := a).
      repeat split; assumption.
    * rewrite Heqbc in *.
      apply Fca.
Qed.

(* Slot Strong Supplementation *)
Axiom BA8 : forall x y,
  (exists z, Ps z x) /\ (exists z, Ps z y) ->
    ((~exists z, Ps z x /\ F y z) ->
      (exists z, Ps z y /\ ~Ps z x)).

(* Slot Weak Supplementation *)
Theorem BT13 : forall x y,
  (PP x y -> (exists z, Ps z y /\ ~ Ps z x)).
Proof.
  intros a b [[c [Fac Pscb]] nPba].
  pose proof (whole_improper_slots b).
  destruct H.
  exists c.
  exact Pscb.
  exists x.
  split.
  apply H.
  intro h.
  apply nPba.
  destruct H.
  exists x.
  split; assumption.
Qed.

(* Slot Extensionality *)
(* This is not a theorem of the theory. *)
Theorem BT14 : forall x y,
  ((exists z, PP z x) \/ (exists z, PP z y)) ->
    ((x = y) <->
      (exists z, PPs z x <-> PPs z y)).
Abort.

(**********************
 *                    *
 * Tarbouriech et al. *
 *                    *
 **********************)

(* Anti-Inheritance *)
Axiom anti_inheritance : forall x y s t,
  x <> y /\ Ps s y /\ F x s /\ Ps t x -> ~Ps t y.

(* Single Owner *)
Axiom single_owner : forall s x,
  Ps s x -> forall y, Ps s y -> x = y.

Definition IPs x y := Ps x y /\ F y x.

(* Slots are either proper or improper. *)
Theorem either_proper_or_improper : forall s x,
  Ps s x -> PPs s x /\ ~IPs s x \/ ~PPs s x /\ IPs s x.
Proof.
  intros s x Pssx.
  destruct (classic (F x s)) as [yesF|notF];
  [right|left];
  repeat split; try assumption;
  apply or_not_and;
  right;
  intuition.
Qed.

(* Improper Slots are only owned by their Filler *)
Theorem unique_owner_improper_slot : forall x s,
  IPs s x -> (forall y, Ps s y -> x = y).
Proof.
  intros x s [Pssx Fxs] y Pssy.
  pose proof (single_owner s y Pssy) as UniqueOwner.
  apply UniqueOwner in Pssx as H.
  rewrite H in UniqueOwner.
  symmetry; assumption.
Qed.

(* *)
Theorem proper_part_in_proper_slot : forall x y,
  PP y x -> (exists s, Ps s x /\ F y s /\ ~Ps s y).
Proof.
  intros x y [[s [Fys Pssx]] nPxy].
  exists s.
  repeat split; try assumption.
  intro Pssy.
  destruct nPxy.
  pose proof (single_owner s x Pssx) as UniqueSOwner.
  apply UniqueSOwner in Pssy.
  rewrite <- Pssy.
  apply BT9.
  exists s; assumption.
Qed.

(* Additional Improper Parthood Slots *)
Axiom A3 : forall x s, F x s -> exists t, IPs t x.

(* General Conditional Reflexivity *)
Theorem general_conditional_refl : forall x,
  (exists s, (Ps s x \/ F x s)) -> P x x.
Proof.
  unfold P.
  intros x [s []].
  - pose proof (whole_improper_slots x).
    destruct H0.
    exists s.
    apply H.
    exists x0.
    apply and_comm.
    apply H0.
  - pose proof (A3 x s).
    destruct H0.
    apply H.
    unfold IPs in H0.
    exists x0.
    apply and_comm.
    assumption.
Qed.

(* Only One Improper Slot per Filler *)
Axiom unique_improper_slot : forall x s t,
  Ps s x -> F x s -> Ps t x -> F x t
    -> s = t.

(***************
 * Composition *
 ***************)

Parameter C : Entity -> Entity -> Entity -> Prop.

(* Composition Existence *)
Axiom composition_existence : forall s t y,
  ((F y s /\ Ps t y) -> (exists u, C u s t)).

Axiom composition_constraints : forall s t u,
  (C u s t -> (exists y, F y s /\ Ps t y)).

(* Composition Unicity *)
Axiom composition_unicity : forall s t u v,
  C u s t /\ C v s t -> u = v.

Axiom composition_semi_func : forall s t u v,
  C v s t /\ C v s u -> t = u.

(* Same Filler *)
Axiom composition_same_filler : forall u s t,
  C u s t -> (exists x, F x u /\ F x t).

(* Same Owner *)
Axiom composition_same_owner : forall u s t,
  C u s t -> (exists x, Ps u x /\ Ps s x).

(* Conditional Non-Commutativity *)
Theorem conditional_no_commutativity : forall s t,
  ((exists u, (C u s t /\ s <> t)) -> ~(exists u', C u' t s)).
Proof.
  intros t u [s []] [v].
  apply composition_constraints in H as [x []].
  apply composition_constraints in H1 as [y []].
  pose proof (mutual_occupancy x y t u (conj (conj H3 H) (conj H2 H1))).
  rewrite <- H4 in H1, H3.
  clear H4 y.
  pose proof (unique_improper_slot x t u H3 H H2 H1).
  contradiction.
Qed.

(* Composition Associativity *)
Axiom composition_associativity : forall s t u a b c d,
  ((C a s t /\ C b a u) /\ (C d s c /\ C c t u) -> b = d).

(* Proper-Improper Composition *)
Axiom pro_imp_composition : forall s t x,
  (IPs s x /\ F x t -> C t t s).

(* Improper-Proper Composition *)
Axiom imp_pro_composition : forall s t x,
  (IPs s x /\ Ps t x -> C t s t).
  
(* Improper-Improper Composition *)
Theorem imp_imp_composition : forall s x,
  (IPs s x -> C s s s).
Proof.
  intros s x IPssx.
  assert (H := IPssx).
  destruct H as [Pssx Fxs].
  pose proof (imp_pro_composition s s x (conj IPssx Pssx)).
  assumption.
Qed.

(****************
 * Part of Slot *
 ****************)

Definition PoS s t := exists u, C s t u.

(* Conditional PoS Reflexivity *)
Theorem conditional_pos_refl : forall s x,
  Ps s x -> PoS s s.
Proof.
  intros.
  unfold PoS.
  apply single_occupancy in H as [z [Fzs UniqueFzs]].
  pose proof (general_conditional_refl z) as [].
  exists s.
  right.
  assumption.
  exists x0.
  pose proof (pro_imp_composition x0 s z).
  unfold IPs in H0.
  apply H0.
  destruct H.
  repeat split.
  all: assumption.
Qed.

(* PoS Anti-Symmetry *)
Theorem pos_antisym : forall s t,
  PoS s t /\ PoS t s -> s = t.
Proof.
  intros s t [[u Cstu][v Ctsv]].
  pose proof (composition_same_owner s t u Cstu) as [w [Pssw Pstw]].
  pose proof (single_occupancy s w Pssw) as [a [_ UniqueFs]].
  pose proof (single_occupancy t w Pstw) as [b [_ UniqueFt]].
  clear Pssw Pstw w.
  
  pose proof (composition_same_filler s t u Cstu) as [a1 [Fas Fau]].
  pose proof (composition_constraints s v t Ctsv) as [a2 [Fa2s Psva]].
  apply UniqueFs in Fas as a_eq_a1, Fa2s as a_eq_a2.
  rewrite <- a_eq_a1 in Fas, Fau.
  rewrite <- a_eq_a2 in Psva.
  clear UniqueFs a_eq_a1 a1 a_eq_a2 Fa2s a2.
  
  pose proof (composition_same_filler t s v Ctsv) as [b1 [Fbt Fbv]].
  pose proof (composition_constraints t u s Cstu) as [b2 [Fb2t Psub]].
  apply UniqueFt in Fbt as b_eq_b1, Fb2t as b_eq_b2.
  rewrite <- b_eq_b1 in Fbt, Fbv.
  rewrite <- b_eq_b2 in Psub.
  clear UniqueFt Fbt b_eq_b1 b1 b_eq_b2 Fb2t b2 .
  
  pose proof (mutual_occupancy a b u v (conj (conj Psub Fau) (conj Psva Fbv))) as a_eq_b.
  rewrite <- a_eq_b in Fbv, Psub.
  clear b a_eq_b .
  
  pose proof (unique_improper_slot a u v Psub Fau Psva Fbv) as u_eq_v.
  rewrite <- u_eq_v in Ctsv, Psva, Fbv.
  rename Ctsv into Ctsu.
  rename Psva into Psua.
  clear v u_eq_v Psub Fbv.
  
  pose proof (pro_imp_composition u s a (conj (conj Psua Fau) Fas)) as Cssu.
  pose proof (composition_unicity s u s t (conj Cssu Ctsu)); assumption.
Qed.

(* PoS Transitivity *)
Theorem pos_trans : forall s t u,
  PoS s t /\ PoS t u -> PoS s u.
Proof.
  intros s t u [[v Cstv][w Ctuw]]; move w before v. 
  unfold PoS.
  (* Owner of s, t and u *)
  pose proof (composition_same_owner s t v Cstv) as [a1 [Pssa1 Psta1]]; move a1 before w.
  pose proof (composition_same_owner t u w Ctuw) as [a2 [Psta2 Psua2]]; move a2 before a1.
  pose proof (single_owner t a1 Psta1) as UniquePsa.
  apply UniquePsa in Psta2 as a_eq_a2.
  rewrite <- a_eq_a2 in Psua2.
  rename a1 into a, Pssa1 into Pssa, Psua2 into Psua, Psta1 into Psta.
  clear a_eq_a2 a2 Psta2 UniquePsa.
  (* Fillers of s, t and u *)
  pose proof (single_occupancy s a Pssa) as [d [Fds UniqueFs]]; move d before a.
  pose proof (single_occupancy t a Psta) as [c [Fct UniqueFt]]; move c before a.
  pose proof (single_occupancy u a Psua) as [b [Fbu UniqueFu]]; move b before a.
  (* Fillers of v and w *)
  pose proof (composition_same_filler s t v Cstv) as [d' [d_eq_d' Fdv]].
  apply UniqueFs in d_eq_d'.
  rewrite <- d_eq_d' in Fdv.
  clear d' d_eq_d'.
  pose proof (composition_same_filler t u w Ctuw) as [c' [c_eq_c' Fcw]].
  apply UniqueFt in c_eq_c'.
  rewrite <- c_eq_c' in Fcw.
  clear c' c_eq_c'.
  (* *)
  pose proof (composition_constraints t v s Cstv) as [c' [c_eq_c' Psvc]].
  apply UniqueFt in c_eq_c'.
  rewrite <- c_eq_c' in Psvc.
  clear c_eq_c' c'.
  pose proof (composition_constraints u w t Ctuw) as [b' [b_eq_b' Pswb]].
  apply UniqueFu in b_eq_b'.
  rewrite <- b_eq_b' in Pswb.
  clear b_eq_b' b'.
  (* *)
  pose proof (composition_existence w v c (conj Fcw Psvc)) as [y Cywv]; move y before w.
  pose proof (composition_same_owner y w v Cywv) as [b' [Psyb b_eq_b']].
  pose proof (single_owner w b Pswb) as UniquePsw.
  apply UniquePsw in b_eq_b'.
  rewrite <- b_eq_b' in Psyb.
  clear UniquePsw b_eq_b' b'.
  (* *)
  exists y.
  pose proof (composition_existence u y b (conj Fbu Psyb)) as [s' Cs'uy].
  pose proof (composition_associativity u w v t s y s' (conj (conj Ctuw Cstv) (conj Cs'uy Cywv))) as s_eq_s'.
  rewrite <- s_eq_s' in Cs'uy.
  assumption.
Qed.

Theorem slots_are_parts_of_imp_slot :
  forall s t x, IPs s x -> Ps t x -> PoS t s.
Proof.
  intros s t x H.
  unfold PoS.
  exists t.
  apply imp_pro_composition with (x:=x).
  split; assumption.
Qed.

Theorem pos_same_owner :
  forall s t, PoS s t -> exists x, Ps s x /\ Ps t x.
Proof.
  intros s t [u Cstu].
  apply composition_same_owner with (u:=s) (s:=t) (t:=u).
  assumption.
Qed.

(* *)
Theorem slots_constrain_fillers : forall a b s t,
  F b t /\ F a s /\ PoS t s -> P b a.
Proof.
  intros a b s t [Fbt [Fas [u Ctsu]]].
  pose proof (composition_constraints s u t Ctsu) as [a' [H H0]].
  pose proof (composition_same_owner t s u Ctsu) as [z [Pstz Pssz]].
  pose proof (single_occupancy s z Pssz) as [a'' [H1 H2]].
  apply H2 in Fas as a''_eq_a, H as a''_eq_a'.
  rewrite a''_eq_a in a''_eq_a'.
  rewrite <- a''_eq_a' in H0.
  clear a''_eq_a a''_eq_a' H1 H2 H a'' a'.
  pose proof (composition_same_filler t s u Ctsu) as [x [H H1]].
  pose proof (single_occupancy t z Pstz) as [x0 [H2 H3]].
  apply H3 in Fbt as x0_eq_b, H as x0_eq_x.
  rewrite x0_eq_x in x0_eq_b.
  rewrite x0_eq_b in H1.
  clear H2 H3 x0_eq_b x0_eq_x H.
  unfold P.
  exists u.
  split; assumption.
Qed.

(* *)
Theorem fillers_constrain_slots : forall a b,
  (P b a -> exists s t, (F b t /\ F a s /\ PoS t s)).
Proof.
  intros a b [t []].
  pose proof (whole_improper_slots a).
  destruct H1 as [s []].
  exists t; assumption.
  exists s, t.
  repeat split; try assumption.
  unfold PoS.
  exists t.
  apply imp_pro_composition with (x:=a).
  unfold IPs.
  repeat split; assumption.
Qed.

(********************
 * Overlap of Slots *
 ********************)

Definition OoS s t := exists u, PoS u s /\ PoS u t.

(* Conditional OoS Reflexivity *)
Theorem cond_oos_refl : forall s x,
  Ps s x -> OoS s s.
Proof.
  intros s x Pssx.
  unfold OoS.
  exists s.
  apply conditional_pos_refl in Pssx.
  split; assumption.
Qed.

(* OoS Symmetry *)
Theorem oos_symmetry : forall s t,
  OoS s t -> OoS t s.
Proof.
  unfold OoS.
  intros.
  destruct H as [x H].
  exists x.
  apply and_comm.
  assumption.
Qed.

(* OoS Same Owner *)
Theorem oos_same_owner : forall s t,
  OoS s t -> (exists x, Ps s x /\ Ps t x).
Proof.
  intros s t [x [PoSxs PoSxt]].
  apply pos_same_owner in PoSxs as [sOwner []].
  apply pos_same_owner in PoSxt as [tOwner []].
  pose proof (single_owner x sOwner H).
  apply H3 in H1.
  rewrite <- H1 in H2.
  exists sOwner.
  split; assumption.
Qed.

Theorem oos_pseudo_trans:
  forall s t u, OoS u t /\ PoS t s -> OoS u s.
Proof.
  unfold OoS.
  intros s t u [[v [PoSvu PoSvt]] PoSts].
  pose proof (pos_trans v t s (conj PoSvt PoSts)).
  exists v.
  split; assumption.
Qed.

Theorem slots_overlap_with_imp_slot :
  forall s t x, IPs s x /\ Ps t x -> OoS s t.
Proof.
  intros s t x [IPssx Pstx].
  unfold OoS, PoS.
  exists t.
  split.
  - exists t.
    apply imp_pro_composition with (x:=x).
    split; assumption.
  - pose proof (single_occupancy t x Pstx) as [y [Fyt _]].
    pose proof (A3 y t Fyt) as [u IPsuy].
    exists u.
    apply pro_imp_composition with (x:=y).
    split; assumption.
Qed.

(****************
 * Sum of Slots *
 ****************)
 
Definition SoS u s t := forall v,
  ((OoS u v) <-> (OoS s v \/ OoS t v)).

(* Sum Existence *)
Axiom sum_existence : forall s t,
  (exists x, (Ps s x /\ Ps t x)) -> (exists u, (SoS u s t)).

(* Sum Unicity *)
Axiom sum_unicity : forall s t u v,
  (SoS u s t /\ SoS v s t -> u = v).

(* Sum Commutativity *)
Theorem sum_commutativity : forall s t u,
  SoS u s t <-> SoS u t s.
Proof.
  intros s t u.
  unfold SoS.
  setoid_rewrite (or_comm (OoS s _)).
  reflexivity.
Qed.

(* Sum Associativity *)
Theorem sum_associativity : forall s t u a b c d,
  ((SoS a s t /\ SoS b a u) /\ (SoS d s c /\ SoS c t u) -> b = d).
Proof.
  intros s t u a b c d.
  unfold SoS.
  intros [[][]].
  apply sum_unicity with (s:=s) (t:=c).
  unfold SoS.
  setoid_rewrite H0.
  setoid_rewrite H.
  setoid_rewrite H1.
  setoid_rewrite H2.
  intuition.
Qed.

(* Sum Idempotence *)
Theorem sum_idempotence : forall s, SoS s s s.
Proof.
  intros s v.
  split; intro.
  - left; assumption.
  - destruct H; assumption.
Qed.

Theorem sum_imp_slot : 
  forall s t x, IPs s x /\ Ps t x -> SoS s s t.
Proof.
  intros s t x [].
  unfold SoS.
  intros v.
  split.
  - intro OoSsv.
    left; assumption.
  - intros.
    destruct H1.
    + assumption.
    + pose proof (oos_same_owner t v H1) as [].
      apply slots_overlap_with_imp_slot with (x:=x).
      split.
      * assumption.
      * destruct H2.
        pose proof (single_owner t x H0).
        apply H4 in H2 as H5.
        rewrite H5.
        assumption.
Qed.

(* Sum Same Owner *)
Theorem sum_same_owner : forall s t u,
  (SoS u s t -> exists x, (Ps u x /\ Ps s x /\ Ps t x)).
Proof.
  intros s t u.
  unfold SoS.
  intros [].  
Admitted.

(***********************
 * Composition And Sum *
 ***********************)

Theorem comp_sum_same_owner : forall a b c s t u x,
  Ps s x -> C a s t -> C b s u -> SoS c a b -> Ps c x.
Proof.
  intros.
  pose proof (composition_same_owner a s t H0) as [x0 []].
  pose proof (sum_same_owner a b c H2) as [x1 [H5 []]].
  pose proof (single_owner s x H).
  apply H8 in H4.
  rewrite <- H4 in H3.
  pose proof (single_owner a x H3).
  apply H9 in H6.
  rewrite <- H6 in H5, H7.
  assumption.
Qed.

Theorem improper_left_distributivity: forall x s t u a b c d e,
  IPs s x -> SoS a t u -> C b s a -> C c s t -> C d s u -> SoS e c d -> b = e.
Proof.
  intros x s t u a b c d e [Pssx Fxs] SoSatu Cbsa Ccst Cdsu SoSecd.
  pose proof (composition_constraints s t c Ccst) as [x0 []].
  pose proof (single_occupancy s x Pssx) as [x1 [_ UniqueFs]].
  apply UniqueFs in Fxs as x1_eq_x.
  apply UniqueFs in H.
  rewrite <- H in H0.
  rewrite x1_eq_x in H0.
  clear UniqueFs H x1_eq_x x1 x0.
  pose proof (sum_same_owner t u a SoSatu) as [x0 [H []]].
  pose proof (single_owner t x H0).
  apply H3 in H1.
  rewrite <- H1 in H, H2.
  clear H1 H3 x0.
  pose proof (imp_pro_composition s a x (conj (conj Pssx Fxs) H)) as Casa.
  pose proof (composition_unicity s a b a (conj Cbsa Casa)).
  rewrite H1.
  clear H1 Cbsa b.
  pose proof (imp_pro_composition s t x (conj (conj Pssx Fxs) H0)) as Ctst.
  pose proof (composition_unicity s t c t (conj Ccst Ctst)).
  rewrite H1 in SoSecd.
  clear H1 Ccst c.
  pose proof (imp_pro_composition s u x (conj (conj Pssx Fxs) H2)) as Cusu.
  pose proof (composition_unicity s u d u (conj Cdsu Cusu)).
  rewrite H1 in SoSecd.
  clear H1 Cdsu d.
  pose proof (sum_unicity t u a e (conj SoSatu SoSecd)).
  assumption.
Qed.

Theorem left_distributivity: forall s t u a b c d e,
  SoS a t u -> C b s a -> C c s t -> C d s u -> SoS e c d -> b = e.
Proof.
  intros s t u a b c d e Satu Cbsa Ccst Cdsu Secd.
  unfold SoS in Satu, Secd.
  unfold OoS in Satu, Secd.
  unfold PoS in Satu, Secd.
Admitted.

(*******************
 * Supplementation *
 *******************)

Theorem full_overlap_is_identity:
  forall s t, (forall u, OoS s u <-> OoS t u) -> s = t.
Proof.
  intros s t H.
  apply sum_unicity with (s:=s) (t:=t).
  split; intros v; rewrite H; intuition.
Qed.

Lemma at_least_two_proper_slots : forall s t x,
  IPs s x -> PPs t x -> (forall v, PPs v x -> t = v) -> forall u, OoS s u <-> OoS t u.
Proof.
  intros s t x [Pssx Fxs] [Pstx nFxt] UniquePPsx u.
  split.
  2: {
    intros.
    apply oos_symmetry.
    apply oos_symmetry in H.
    apply oos_pseudo_trans with (s:=s) (t:=t) (u:=u).
    split.
    + assumption.
    + apply slots_are_parts_of_imp_slot with (x:=x).
      repeat split; assumption.
      assumption.
  }
  - intros.
    unfold OoS.
    destruct H as [v []].
    exists v.
    split; try assumption.
    pose proof (pos_same_owner v s H) as [x0 []].
    pose proof (single_owner s x Pssx).
    apply H3 in H2.
    rewrite <- H2 in H1.
    clear H2 H3.
    pose proof (either_proper_or_improper v x H1).
    destruct H2.
    + destruct  H2.
      apply UniquePPsx in H2.
      rewrite <- H2.
      apply conditional_pos_refl with (x:=x).
      assumption.
    + destruct H2.
      destruct H3.
      pose proof (unique_improper_slot x s v Pssx Fxs H3 H4).
      rewrite <- H5 in *.
      clear H5 v.
      pose proof (slots_are_parts_of_imp_slot s t x (conj Pssx Fxs) Pstx).
Abort.

Theorem slot_company:
  forall s x, PPs s x -> exists t, PPs t x /\ s <> t. 
Proof.
  intros s x [Pssx nFxs].
  pose proof (whole_improper_slots x) as [Sx [PsSxx FxSx]].
  exists s; assumption.
Admitted.

Theorem slot_weak_supplementation :
  forall s x, PPs s x -> exists t, Ps t x /\ ~ (OoS s t).
Proof.
  intros s x PPsx.
Admitted.
