From demo Require Import simplified_iris.

Section proof.
Context `{!heapGS Σ}.

Theorem coq_swap (P Q: Prop):
  P ∧ Q → Q ∧ P.
Proof.
  intros H.
  destruct H as [HP HQ].
  split.
  - apply HQ.
  - apply HP.
Qed.

Theorem prove_swap_the_hard_way x y :
  x ↦ #0 ∗ y ↦ #3 ⊢ y ↦ #3 ∗ x ↦ #0.
Proof.
  iIntros "H".
  iDestruct "H" as "[Hx Hy]".
  iSplitL "Hy".
  - iApply "Hy".
  - iApply "Hx".
Qed.

Theorem prove_swap_the_easy_way x y :
  x ↦ #0 ∗ y ↦ #3 ⊢ y ↦ #3 ∗ x ↦ #0.
Proof.
  iIntros "[Hx Hy]".
  iFrame.
Qed.

Theorem ex01 (x y: loc) :
  x ↦ #0 ∗ y ↦ #0 ⊢ WP #x <- #y;; #y <- #x {{ λ _, x ↦ #y ∗ y ↦ #x }}.
Proof.
  iIntros "[Hx Hy]".
  wp_bind (Store _ _).
  iApply wp_frame.
  iSplitL "Hx".
  { iApply (wp_store_axiom with "Hx"). }
  simpl. iIntros (?) "Hx"; wp_pures.
  iApply wp_frame.
  iSplitL "Hy".
  { iApply (wp_store_axiom with "Hy"). }
  simpl. iIntros (?) "Hy".
  iFrame.
Qed.

End proof.
