Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition contains_substring (substring s : string) : Prop :=
  exists pre post, s = String.append pre (String.append substring post).

Inductive filtered (P : string -> Prop) : list string -> list string -> Prop :=
| filtered_nil : filtered P [] []
| filtered_cons_true : forall x l l', P x -> filtered P l l' -> filtered P (x :: l) (x :: l')
| filtered_cons_false : forall x l l', ~ P x -> filtered P l l' -> filtered P (x :: l) l'.

Definition filter_by_substring_spec (strings : list string) (substring : string) (res : list string) : Prop :=
  filtered (contains_substring substring) strings res.

Example test_case : filter_by_substring_spec ["abc"; "bcd"; "cbd"; "dbc"; "cda"] "bc" ["abc"; "bcd"; "dbc"].
Proof.
  unfold filter_by_substring_spec.
  apply filtered_cons_true.
  - exists "a", "". reflexivity.
  - apply filtered_cons_true.
    + exists "", "d". reflexivity.
    + apply filtered_cons_false.
      * intros [pre [post H]].
        destruct pre; simpl in H.
        { discriminate. }
        { injection H as _ H.
          destruct pre; simpl in H.
          { injection H as _ H. discriminate. }
          { injection H as _ H.
            destruct pre; simpl in H.
            { discriminate. }
            { injection H as _ H.
              destruct pre; simpl in H; discriminate.
            }
          }
        }
      * apply filtered_cons_true.
        -- exists "d", "". reflexivity.
        -- apply filtered_cons_false.
           ++ intros [pre [post H]].
              destruct pre; simpl in H.
              { discriminate. }
              { injection H as _ H.
                destruct pre; simpl in H.
                { discriminate. }
                { injection H as _ H.
                  destruct pre; simpl in H.
                  { discriminate. }
                  { injection H as _ H.
                    destruct pre; simpl in H; discriminate.
                  }
                }
              }
           ++ apply filtered_nil.
Qed.