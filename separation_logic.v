From iris.proofmode Require Import proofmode.

Section logic_examples.
  Context {PROP : bi}.

  Lemma classic1 (P Q : Prop) :
    P ∧ Q → Q ∧ P.
  Proof.
    intros [HP HQ].
    split.
    - apply HQ.
    - apply HP.
  Qed.

  (* Replace ∧ with ∗, and → with -∗. *)
  Lemma linear1 (P Q : PROP) :
    P ∗ Q -∗ Q ∗ P.
  Proof.
    iIntros "[HP HQ]".
    iSplitL "HQ".
    - iApply "HQ".
    - iApply "HP".
  Qed.

  Lemma classic2 (P : Prop) :
    P → P ∧ P.
  Proof.
    intros HP.
    split.
    - apply HP.
    - apply HP.
  Qed.

  Lemma linear2 (P : PROP) :
    P -∗ P ∗ P.
  Proof.
    iIntros "HP".
    iSplitL "HP".
    - iApply "HP".
    - (* HP has already been consumed to prove the left-hand P. *)
  Abort.

  Lemma classic3 (P Q R : Prop) :
    P ∧ (P → Q) ∧ (Q → R) → R.
  Proof.
    intros (HP & HPQ & HQR).
    apply HQR.
    apply HPQ.
    apply HP.
  Qed.

  Lemma linear3 (P Q R : PROP) :
    P ∗ (P -∗ Q) ∗ (Q -∗ R) -∗ R.
  Proof.
    iIntros "(HP & HPQ & HQR)".
    iApply "HQR".
    iApply "HPQ".
    iApply "HP".
  Qed.

  Lemma classic4 (P Q R : Prop) : 
    P ∧ Q ∧ (P → R) → Q ∧ R.
  Proof.
    intros (HP & HQ & HF).
    split.
    - apply HQ.
    - apply HF. apply HP.
  Qed.

  Lemma linear4 (P Q R : PROP) : 
    P ∗ Q ∗ (P -∗ R) -∗ Q ∗ R.
  Proof.
    iIntros "(HP & HQ & HF)".
    (* Split the assumptions (resources) as well *)
    iSplitL "HQ".
    - iApply "HQ".
    - iApply "HF".
      iApply "HP".
  Qed.

End logic_examples.