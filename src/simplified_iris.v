From iris.heap_lang Require Export proofmode notation.

(* make these print *)
Notation NONE := (InjL (LitV LitUnit)).
Notation NONEV := (InjLV (LitV LitUnit)).
Notation SOME x := (InjR x).
Notation SOMEV x := (InjRV x).

#[export] Set Default Goal Selector "!".
#[export] Set Default Proof Using "Type".

Section proof.
Context `{!heapGS Σ}.

Lemma wp_frame (e: expr) (Φ Φ': val → iProp Σ) :
  WP e {{Φ}} ∗ (∀ r, Φ r -∗ Φ' r) ⊢ WP e {{Φ'}}.
Proof.
  iIntros "[Hwp Himpl]".
  iApply (wp_strong_mono with "Hwp [Himpl]").
  - auto.
  - auto.
  - iIntros (v) "HΦ !>".
    iApply "Himpl"; auto.
Qed.

Lemma wp_store_axiom (l: loc) (v0 v: val) :
  l ↦ v0 ⊢ WP (#l <- v) {{ λ _, l ↦ v }}.
Proof. iIntros "Hl". wp_store. auto. Qed.

Lemma wp_load_axiom (l: loc) (v: val) :
  l ↦ v ⊢ WP ! #l {{ λ r, ⌜r = v⌝ ∗ l ↦ v }}.
Proof. iIntros "Hl". wp_load. auto. Qed.

Lemma wp_free_axiom (l: loc) (v: val) :
  l ↦ v ⊢ WP Free #l {{ λ _, emp }}.
Proof. iIntros "Hl". wp_free. auto. Qed.

End proof.
