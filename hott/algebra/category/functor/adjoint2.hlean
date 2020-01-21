
import .equivalence

open eq functor nat_trans prod prod.ops

namespace category


  variables {C D E : Precategory} (F : C ⇒ D) (G : D ⇒ C) (H : D ≅c E)
(*
Definition adjoint_compose (K : F ⊣ G)
    : H of F ⊣ G of H^-1ᴱ.
Proof.
    fconstructor,
    { fapply change_natural_map,
      { exact calc
          1 ⟹ G of F                 : to_unit K
        ... ⟹ (G of 1) of F          : !id_right_natural_rev onf F
        ... ⟹ (G of (H^-1 of H)) of F : (G ofn unit H) onf F
        ... ⟹ ((G of H^-1) of H) of F : !assoc_natural onf F
        ... ⟹ (G of H^-1) of (H of F) : assoc_natural_rev},
      { intro c, esimp, exact G (unit H (F c)) o to_unit K c},
      { intro c, rewrite [▸*, +id_left]}},
    { fapply change_natural_map,
      { exact calc
        (H of F) of (G of H^-1)
            ⟹ ((H of F) of G) of H^-1 : assoc_natural
        ... ⟹ (H of (F of G)) of H^-1 : !assoc_natural_rev onf H^-1
        ... ⟹ (H of 1) of H^-1        : (H ofn to_counit K) onf H^-1
        ... ⟹ H of H^-1               : !id_right_natural onf H^-1
        ... ⟹ 1                      : counit H},
      { intro e, esimp, exact counit H e o to_fun_hom H (to_counit K (H^-1 e))} =>
      { intro c, rewrite [▸*, +id_right, +id_left]}},
    { intro c, rewrite [▸*, +respect_comp], refine !assoc @ ap (fun x => x o _) !assoc^-1 @ _,
      rewrite [-respect_comp],
      },
    { }
Defined.
*)
Defined. category
