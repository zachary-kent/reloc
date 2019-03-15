(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Treiber stack *)
From reloc Require Export reloc lib.list.

(** In the Treiber stack each node is a reference that we can CAS on *)
Notation Conse h t := (ref (SOME (h, t)))%E.
Notation Nile := (ref NONE)%E.

Definition FG_push : val := rec: "push" "st" := λ: "x",
  let: "stv" := !"st" in
  if: (CAS "st" "stv" (Conse "x" "stv"))
  then #()
  else "push" "st" "x".

(* pop st = λ (),
     (λ str.
       (λ x. match x with
             | nil => InjL #()
             | cons y ys =>
               if CAS(st, str, ys)
                  (InjR y)
                  (pop st ()))
       (load str))
     (load st)*)
Definition FG_pop : val := rec: "pop" "st" :=
  let: "stv" := !"st" in
  let: "x" := !(rec_unfold "stv") in
  match: "x" with
    InjL <> => InjL #()
  | InjR "x" => let: "y" := Fst "x" in let: "ys" := Snd "x" in
                if: (CAS "st" "stv" "ys")
                then (InjR "y")
                else "pop" "st"
  end.

Definition FG_new_stack : val := λ: <>, ref Nile.

Definition FG_stack : val := Λ:
  (FG_new_stack, λ: "st", FG_pop "st", λ: "st" "x", FG_push "st" "x").
