Lemma nat_ind2 : forall P,
    P 0 0 ->
    (forall x, P x 0 -> P (S x) 0) ->
    (forall y, P 0 y -> P 0 (S y)) ->
    (forall x y, P x y -> P (S x) (S y)) ->
    forall x y, P x y.
Proof.
  intros P P0 Px Py Pxy x.
  induction x; intros y; induction y.
  - exact P0.
  - apply Py.
    exact IHy.
  - apply Px.
    exact (IHx 0).
  - apply Pxy.
    exact (IHx y).
Qed.

Ltac ind_nat2 x y :=
  revert x y;
  match goal with
  | [ |- forall x y, ?H ] => apply (nat_ind2 (fun x y => H))
  end.