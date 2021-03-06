Require Export Denotational.
Require Import Advance.
Require Import Tactics.
Require Import Equality.
Open Scope Z.

(********** Monotonicity of the denotational semantics **********)

Lemma adv_inp_monotone A (in1 in2 : inp A) n : in1 ⊆ in2 -> adv_inp n in1 ⊆ adv_inp n in2.
Proof. 
  unfold lep, adv_inp. simpl. intros. remember (in1 (n + i) j) as X.
  destruct X;tryfalse. apply H. rewrite <- H0. auto. 
Qed.

Lemma lep_vcons A n (v1 v2 : vector (option A) n) x1 x2 :
  x1 ⊆ x2 -> v1 ⊆ v2 -> (x1 :: v1) ⊆ (x2 :: v2).
Proof.
  intros. intros. simpl. intros. dependent destruction i.
  auto. simpl in *. auto.
Qed. 
Lemma lep_vnil A : vnil (option A) ⊆ vnil (option A).
Proof. intro. auto. Qed.

Hint Resolve lep_vcons lep_vnil.

Lemma Rsem_monotone' n (vars1 vars2 : vector (option Z) n) e rho1 rho2 : 
  rho1 ⊆ rho2 -> vars1 ⊆ vars2 -> R'[| e |] vars1 rho1 ⊆ R'[| e |] vars2 rho2.
Proof.
  generalize dependent rho1. generalize dependent rho2. 
  generalize dependent vars1. generalize dependent vars2. 
  induction e; try solve [simpl; intros; auto].
  - simpl. intros. 
    remember (R'[|e1|] vars1 rho1) as R1; remember (R'[|e2|] vars1 rho1) as R2.
    destruct R1;destruct R2; tryfalse.
    symmetry in HeqR1. eapply IHe1 in HeqR1.
    symmetry in HeqR2. eapply IHe2 in HeqR2.
    rewrite HeqR1. rewrite HeqR2. auto. auto. auto. auto. auto.
  - simpl. intros. remember (R'[|e|] vars1 rho1) as R.
    destruct R; tryfalse.
    symmetry in HeqR. eapply IHe in HeqR.
    rewrite HeqR. auto. auto. auto.
  - simpl. intros. 
    remember (adv_inp (- Z.of_nat n0) rho1) as rho1'. 
    remember (adv_inp (- Z.of_nat n0) rho2) as rho2'. 
    assert (rho1' ⊆ rho2') as Sub.
    subst. apply adv_inp_monotone. auto.
    clear Heqrho1' Heqrho2'.
    generalize dependent z. induction n0.
    + simpl in *. eapply IHe2; eauto. 
    + intros. simpl. eapply IHe1. apply adv_inp_monotone. eauto.
      apply lep_vcons;auto. simpl. intros. apply IHn0; auto. apply H2.
      simpl. apply H0. apply H1.
Qed.

Corollary Rsem_monotone  e rho1 rho2 : rho1 ⊆ rho2 -> R[| e |]rho1 ⊆ R[| e |]rho2.
Proof. intros. apply Rsem_monotone'; auto. Qed.

Lemma Bsem_monotone e rho1 rho2 : rho1 ⊆ rho2 -> B[| e |]rho1 ⊆ B[| e |]rho2.
Proof.
  intro S; induction e; simpl; intros; auto.
  - destruct S. auto.
  - destruct S as [S1 S2]. 
    remember (R[|r|](fst rho1)) as X1. remember (R[|r0|](fst rho1)) as X2.
    pose (Rsem_monotone r _ _ S1) as R1. pose (Rsem_monotone r0 _ _ S1) as R2.
    destruct X1; tryfalse. destruct X2; tryfalse. 
    rewrite <- HeqX1 in R1. rewrite <- HeqX2 in R2.
    simpl in *. erewrite R1 by auto. erewrite R2 by auto.
    auto.
  - destruct (B[|e|]rho1); tryfalse. erewrite IHe by auto. assumption.
  - destruct (B[|e1|]rho1); tryfalse. destruct (B[|e2|]rho1); tryfalse.
    erewrite IHe1 by auto. erewrite IHe2 by auto.  assumption.
Qed.


Lemma adv_env_monotone rho1 rho2 n : rho1 ⊆ rho2 -> adv_env n rho1 ⊆ adv_env n rho2.
Proof. 
  intros. destruct rho1. destruct rho2. destruct H. split; apply adv_inp_monotone;
  auto.
Qed.


Theorem Csem_monotone c rho1 rho2 : rho1 ⊆ rho2 -> C[| c |]rho1 ⊆ C[| c |]rho2.
Proof.
  generalize dependent rho1. generalize dependent rho2. 
  induction c; intros rho2 rho1 S; simpl; intros; auto.
  - pose S as S'. destruct S' as [S1 S2]. 
    remember (R[|r|] (fst rho1)) as Y. destruct Y; tryfalse.
    pose (Rsem_monotone r (fst rho1) (fst rho2) S1). 
    unfold scale_trace in *. unfold compose in *.
    rewrite <- HeqY in *. apply lep_some in l. rewrite <- l.
    remember (C[|c|] rho1 i) as X.
    pose (IHc _ _ S i) as IHi. 
    destruct X; tryfalse. rewrite <- HeqX in * by auto. erewrite IHi by auto.
    auto.
  - simpl. apply adv_env_monotone with (n := Z.of_nat n) in S. apply IHc in S.
    simpl in S. unfold delay_trace in *. destruct (leb n i); auto.
  - unfold add_trace, add_trans in *. 
    remember (C[|c1|] rho1 i) as X1. remember (C[|c2|] rho1 i) as X2.
    pose (IHc1 _ _ S i) as IHi1. pose (IHc2 _ _ S i) as IHi2. 
    destruct X1; tryfalse. destruct X2; tryfalse. 
    symmetry in HeqX1. apply IHi1 in HeqX1.
    symmetry in HeqX2. apply IHi2 in HeqX2. 
    auto. erewrite HeqX1. erewrite HeqX2. auto.
  - generalize dependent rho1.
    generalize dependent rho2.
    generalize dependent i.
    induction n; intros.
    * simpl. simpl in H.  remember (B[|b|]rho1) as B.
      pose (Bsem_monotone b (rho1) (rho2) S) as HB. 
      destruct B; tryfalse. symmetry in HeqB. apply HB in HeqB.
      rewrite HeqB. destruct b0. eapply IHc1; eauto.
      eapply IHc2; eauto.
    * simpl. simpl in H. remember (B[|b|]rho1) as B.
      pose (Bsem_monotone b (rho1) (rho2) S) as HB. 
      destruct B; tryfalse. symmetry in HeqB. apply HB in HeqB.
      rewrite HeqB. destruct b0. eapply IHc1; eauto.
      unfold delay_trace in *. destruct (leb 1 i).
      + eapply IHn. apply adv_env_monotone. eassumption. assumption.
      + assumption.
Qed.
