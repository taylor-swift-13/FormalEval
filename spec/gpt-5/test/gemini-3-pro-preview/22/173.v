Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition int := Z.

Inductive Any : Type :=
| AnyInt : Z -> Any
| AnyList : list Z -> Any.

Definition IsInt (v : Any) (n : int) : Prop :=
  match v with
  | AnyInt z => z = n
  | _ => False
  end.

Lemma IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.
Proof.
  intros v n m Hn Hm.
  destruct v; simpl in *; subst; auto.
  contradiction.
Qed.

Inductive filter_integers_rel : list Any -> list int -> Prop :=
| fir_nil : filter_integers_rel [] []
| fir_cons_int v n vs res :
    IsInt v n ->
    filter_integers_rel vs res ->
    filter_integers_rel (v :: vs) (n :: res)
| fir_cons_nonint v vs res :
    (forall n, ~ IsInt v n) ->
    filter_integers_rel vs res ->
    filter_integers_rel (v :: vs) res.

Definition filter_integers_spec (values : list Any) (res : list int) : Prop :=
  filter_integers_rel values res.

Example test_filter_integers_mixed : 
  filter_integers_spec 
    [AnyInt 1; AnyList [4]; AnyList [5]; AnyList [7; 8; 8]; AnyInt 9; AnyList [5]] 
    [1; 9].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n := 1).
  - simpl. reflexivity.
  - apply fir_cons_nonint.
    + intros n H. simpl in H. contradiction.
    + apply fir_cons_nonint.
      * intros n H. simpl in H. contradiction.
      * apply fir_cons_nonint.
        -- intros n H. simpl in H. contradiction.
        -- apply fir_cons_int with (n := 9).
           ++ simpl. reflexivity.
           ++ apply fir_cons_nonint.
              ** intros n H. simpl in H. contradiction.
              ** apply fir_nil.
Qed.