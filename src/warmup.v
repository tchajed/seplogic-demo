From iris.heap_lang Require Export proofmode notation.

Export Set Default Goal Selector "!".
Export Set Default Proof Using "Type".

Section proof.
Context `{!heapG Σ}.

Theorem ex01 (x y: loc) :
  x ↦ #0 ∗ y ↦ #0 ⊢ WP #x <- #y;; #y <- #x {{ λ _, x ↦ #y ∗ y ↦ #x }}.
Proof.
  iIntros "[Hx Hy]".
  wp_apply (wp_store with "Hx").
  iIntros "Hx"; wp_pures.

  (* we're always going to want to give it the same name, so Iris has a tactic
  for that: *)
  wp_store.
  iFrame.
Qed.

End proof.
