From demo Require Import simplified_iris.

Section proof.
Context `{!heapG Σ}.

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
  simpl. iIntros (?) "Hy"; wp_pures.
  iFrame.
Qed.

End proof.
