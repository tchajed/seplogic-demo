From demo Require Import simplified_iris.

(** Warmup: getting used to reading Coq and Iris Proof Mode (IPM) goals.

Coq is fundamentally an interactive tool, which means you have to "step through"
the code and look at the proof state at each step. Without this, it's unusable -
nobody magically writes this code and simulates its effects mentally.
 *)

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

(** This lemma is equivalent to the Hoare triple

{{{ x ↦ #0 ∗ y ↦ #0 }}}
  #x <- #y;; #y <- #x
{{{ RET _; x ↦ #y ∗ y ↦ #x }}}

but expressed using WP, a "weakest precondition".

 *)

Lemma ex01 (x y: loc) :
  x ↦ #0 ∗ y ↦ #0 ⊢
  WP #x <- #y;; #y <- #x
  {{ λ _, x ↦ #y ∗ y ↦ #x }}.
Proof.
  iIntros "[Hx Hy]".

  (* How do we break down this proof? We'll want to first reason about the load,
  then the rest of the program. *)

  wp_bind (_ <- _)%E.
  iApply wp_frame.
  (* The combination of [wp_bind] and [wp_frame] leaves us with two obligations
  to prove _separately_: we pick some ?Goal which is the postcondition for #x <-
  #y, and then get that postcondition as an assumption to prove a WP for the
   rest of the original code. *)

  (* In separation logic, to prove [P ∗ Q] we have to decide how to split our
  resources. We choose to use "Hx" on the left and the rest on the right. *)

  iSplitL "Hx".
  { iApply (wp_store_axiom with "Hx"). }
  iIntros (?) "Hx"; wp_pures.
  iApply wp_frame.
  iSplitL "Hy".
  { iApply (wp_store_axiom with "Hy"). }
  iIntros (?) "Hy".
  iFrame.
Qed.

(** This is a more typical proof, using the Hoare triple notation and more
automation. It is also stronger than [ex01] in that it promises the return value
is #(). *)
Lemma ex01_triple (x y: loc) :
  {{{ x ↦ #0 ∗ y ↦ #0 }}}
  #x <- #y;;
  #y <- #x
  {{{ RET #(); x ↦ #y ∗ y ↦ #x }}}.
Proof.
  iIntros (Φ) "[Hx Hy] HΦ".
  wp_store.
  wp_store.
  iApply ("HΦ" with "[$]").
Qed.

End proof.
