From demo Require Import simplified_iris.

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
      SOME "tree" =>
      (* if this tree has children, delete them first. Recall the tree is just a
      tuple of the left and right child tree pointers. *)
      (let: "left" := Fst "tree" in
       let: "right" := Snd "tree" in
       "delete_tree" "left";;
       "delete_tree" "right";;
      (* then free the root pointer *)
      Free "x")
    | NONE =>
      (* the way we've represented trees, even an empty tree is a pointer to a
      None, so free that, too *)
      Free "x"
    end.

Section proof.

Context `{!heapG Σ}.
Implicit Types (t l r:loc).

(* You can ignore some magic that creates the recursive tree predicate... *)

Definition tree_pre (tree: loc -d> iPropO Σ): loc -d> iPropO Σ :=
  (λ t, t ↦ NONEV ∨ (∃ l r, t ↦ SOMEV (#l, #r) ∗ ▷ tree l ∗ ▷ tree r))%I.

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
  t ↦ NONEV ∨ (∃ l r, t ↦ SOMEV (#l, #r) ∗ ▷ tree l ∗ ▷ tree r).
Proof. apply (fixpoint_unfold tree_pre). Qed.

Theorem wp_delete_tree t :
  tree t -∗
  WP delete_tree #t
  {{ λ _, emp }}.
Proof.
  iIntros "Ht".

  (* First we should understand how Hoare logic proofs are encoded in Iris. In
  the course infrastructure the goal is always a triple (a proc_spec goal). In
  Iris the goal is going to be [WP e {{ Q }}], which is a separation logic
  predicate, not a Coq assertion. For intuition, keep in mind that {{P}} e {{Q}}
  is the same thing as P ⊢ WP e {{ Q }}. Then, you can think of the spec being
  proven as one where the precondition is all of the premises (the hypotheses)
  and the program and postcondition are in the goal. *)

  (* this is how we start a recursive proof: *)
  iLöb as "IH" forall (t).
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
    (* I won't go through the motions of using the frame rule and
    load/store/free axioms; there's a tactic for that *)
    wp_load; wp_pures.
    wp_free.
    auto.
  - (* In the other case we need to further destruct [tree] to get out the left
    and right subtrees (both their root pointers and the corresponding [tree]
    predicates) *)
    iDestruct "Ht" as (l r) "(Ht & Hl & Hr)".
    wp_rec.
    wp_load; wp_pures.

    (* wp_bind is a tactic to apply the sequencing rule (it takes an argument to
    pick what should be sequenced, for example in e1;; e2;; e3 you can isolate
    (e1;;e2) if you want) *)
    wp_bind (delete_tree _).

    (* The recursive calls make use of the inductive hypothesis "IH", which says
    any recursive calls to delete_tree can be assumed to satisfy this
    specification. *)
    iApply wp_frame.
    iSplitL "Hl".
    { iApply ("IH" with "Hl"). }
    (* I'm naming the postcondition from the deletetree specification "Hl" just
    to emphasize what happened (it's an emp and thus unimportant, the equivalent
    of having a hypothesis "True") *)
    simpl; iIntros (?) "Hl"; wp_pures.

    wp_bind (delete_tree _).
    iApply wp_frame.
    iSplitL "Hr".
    { iApply ("IH" with "Hr"). }
    simpl; iIntros (?) "Hr"; wp_pures.
    wp_free.
    auto.
Qed.

End proof.
