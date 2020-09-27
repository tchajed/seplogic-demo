From iris.heap_lang Require Export proofmode notation.

Export Set Default Goal Selector "!".
Export Set Default Proof Using "Type".

(** * deletetree from the Separation Logic CACM paper by O'Hearn *)

(** A tree will be a pointer to either None (represented InjL #()) or Some(l,r)
(represented InjR (l, r)), where l and r are themselves trees. *)

(** delete_tree is a version of the deletetree function from the paper, written
in an OCaml-like language rather than the C code in the paper. *)
Definition delete_tree: val :=
  (* the rec: here starts a recursive function *)
  rec: "delete_tree" "x" :=
    (* !"x" deferences the variable x (variables need to be quoted) *)
    match: !"x" with
      InjR "tree" =>
      (* if this tree has children, delete them first. Recall the tree is just a
      tuple of the left and right child tree pointers. *)
      (let: "left" := Fst "tree" in
       let: "right" := Snd "tree" in
       "delete_tree" "left";;
       "delete_tree" "right";;
      (* then free the root pointer *)
      Free "x")
    | InjL <> =>
      (* the way we've represented trees, even an empty tree is a pointer to a
      None, so free that, too *)
      Free "x"
    end.

Section proof.

Context `{!heapG Σ}.
Implicit Types (t l r:loc).

(* You can ignore some magic that creates the recursive tree predicate... *)

Definition tree_pre (tree: loc -d> iPropO Σ): loc -d> iPropO Σ :=
  (λ t, t ↦ InjLV #() ∨ (∃ l r, t ↦ InjRV (#l, #r) ∗ ▷ tree l ∗ ▷ tree r))%I.

Local Instance tree_pre_contractive : Contractive tree_pre.
Proof.
  rewrite /tree_pre=> n tree tree' Htree t.
  repeat (f_contractive || f_equiv); apply Htree.
Qed.

Definition tree : loc → iProp Σ := fixpoint tree_pre.

(** Following the fixpoint magic above, the definition [tree] ends up being the
recursive definition we expect (the ⊣⊢ means "equivalent"). You can pretend ▷P
is the same as P; it's a technically related to writing recursive predicates in
Iris. *)
Theorem tree_unfold t :
  tree t ⊣⊢
  t ↦ InjLV #() ∨ (∃ l r, t ↦ InjRV (#l, #r) ∗ ▷ tree l ∗ ▷ tree r).
Proof. apply (fixpoint_unfold tree_pre). Qed.

Theorem wp_delete_tree t :
  {{{ tree t }}}
    delete_tree #t
  {{{ RET #(); emp }}}.
Proof.
  (* this is how we start a recursive proof: *)
  iLöb as "IH" forall (t).
  iIntros (Φ) "Ht HΦ".
  (* What we get from iLöb is an assumption that delete_tree follows the
  specification. How is that possible? Couldn't we just use it right away and
  not have to any work? Indeed! That's why this assumption has the ▷ (pronounced
  "later") in front. ▷ P means we only get to know that P holds after one "step"
  within our function. This is enough to handle all the recursive calls but
  can't be used to just dismiss the whole proof (otherwise proofs would be easy
  but not very meaningful) *)

  (* We destruct the tree predicate into the two branches of the [∨], and carry
  out the proof separately in each case. *)
  iDestruct (tree_unfold with "Ht") as "[Ht|Ht]".
  - (* The first case corresponds to an empty tree, where t ↦ None. In that case
    the code reduces down to just executing a Free on the root pointer. *)
    wp_rec.
    wp_load; wp_pures.
    wp_free.
    iApply "HΦ"; auto.
  - (* In the other case we need to further destruct [tree] to get out the left
    and right subtrees (both their root pointers and the corresponding [tree]
    predicates) *)
    iDestruct "Ht" as (l r) "(Ht & Hl & Hr)".
    wp_rec.
    wp_load; wp_pures.
    wp_apply ("IH" with "Hl"); iIntros "_"; wp_pures.
    wp_apply ("IH" with "Hr"); iIntros "_"; wp_pures.
    wp_free.
    iApply "HΦ"; auto.
Qed.

End proof.
