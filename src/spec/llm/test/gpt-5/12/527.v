Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Lia.

Import ListNotations.

Definition longest_spec (strings : list string) (res : option string) : Prop :=
  match strings with
  | [] => res = None
  | _ =>
    exists l1 s l2,
      strings = l1 ++ s :: l2 /\
      res = Some s /\
      (forall t, In t strings -> String.length t <= String.length s) /\
      (forall t, In t l1 -> String.length t < String.length s)
  end.

Example test_longest_spec_case :
  longest_spec
    (["defghijklmnop"%string; ""%string; "r"%string; "defghijklmnop"%string; "Helolo,"%string; "dHelloBonjour,efghijklmnop"%string; "defghijklmnop"%string; "defghijklmnop"%string])
    (Some "dHelloBonjour,efghijklmnop"%string).
Proof.
  unfold longest_spec; simpl.
  exists (["defghijklmnop"%string; ""%string; "r"%string; "defghijklmnop"%string; "Helolo,"%string]).
  exists ("dHelloBonjour,efghijklmnop"%string).
  exists (["defghijklmnop"%string; "defghijklmnop"%string]).
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + split.
      * intros t Hin.
        simpl in Hin.
        destruct Hin as [H|Hin]; [subst; simpl; lia|].
        destruct Hin as [H|Hin]; [subst; simpl; lia|].
        destruct Hin as [H|Hin]; [subst; simpl; lia|].
        destruct Hin as [H|Hin]; [subst; simpl; lia|].
        destruct Hin as [H|Hin]; [subst; simpl; lia|].
        destruct Hin as [H|Hin]; [subst; simpl; lia|].
        destruct Hin as [H|Hin]; [subst; simpl; lia|].
        destruct Hin as [H|Hin]; [subst; simpl; lia|].
        contradiction.
      * intros t Hin.
        simpl in Hin.
        destruct Hin as [H|Hin]; [subst; simpl; lia|].
        destruct Hin as [H|Hin]; [subst; simpl; lia|].
        destruct Hin as [H|Hin]; [subst; simpl; lia|].
        destruct Hin as [H|Hin]; [subst; simpl; lia|].
        destruct Hin as [H|Hin]; [subst; simpl; lia|].
        contradiction.
Qed.