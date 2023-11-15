From iris.heap_lang Require Export proofmode notation.

(** This file isn't shown in the demo, it just supplies a few tools to make the
demo easier to follow. *)

(* make these print *)
Notation NONE := (InjL (LitV LitUnit)).
Notation NONEV := (InjLV (LitV LitUnit)).
Notation SOME x := (InjR x).
Notation SOMEV x := (InjRV x).

#[export] Set Default Goal Selector "!".
#[export] Set Default Proof Using "Type".

Section proof.
Context `{!heapGS Σ}.

(** We prove lemmas corresponding to the typical "axioms" of separation logic.
These are stated in the usual "small footprint" style of presentations of SL.
Iris normally states these in a more complicated but equivalent way that's
easier for interactive proofs. Here we'll do proofs in a more verbose way using
these axioms plus explicit calls to [wp_frame].
*)

Lemma wp_store_axiom (l: loc) (v0 v: val) :
  l ↦ v0 ⊢ WP (#l <- v) {{ λ (_: val), l ↦ v }}.
Proof. iIntros "Hl". wp_store. auto. Qed.

Lemma wp_load_axiom (l: loc) (v: val) :
  l ↦ v ⊢ WP ! #l {{ λ (r: val), ⌜r = v⌝ ∗ l ↦ v }}.
Proof. iIntros "Hl". wp_load. auto. Qed.

Lemma wp_free_axiom (l: loc) (v: val) :
  l ↦ v ⊢ WP Free #l {{ λ (_: val), emp }}.
Proof. iIntros "Hl". wp_free. auto. Qed.

Lemma wp_frame (e: expr) (Φ Φ': val → iProp Σ) :
  WP e {{Φ}} ∗ (∀ (r: val), Φ r -∗ Φ' r) ⊢ WP e {{Φ'}}.
Proof.
  iIntros "[Hwp Himpl]".
  iApply (wp_strong_mono with "Hwp [Himpl]").
  - auto.
  - auto.
  - iIntros (v) "HΦ !>".
    iApply "Himpl"; auto.
Qed.

End proof.
