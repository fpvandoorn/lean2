(*
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

Bundled structures
*)
import algebra.ring
open algebra pointed is_trunc

namespace algebra
structure Semigroup.
(carrier : Type) (struct : semigroup carrier)




structure CommSemigroup.
(carrier : Type) (struct : comm_semigroup carrier)




structure Monoid.
(carrier : Type) (struct : monoid carrier)




structure CommMonoid.
(carrier : Type) (struct : comm_monoid carrier)




structure Group.
(carrier : Type) (struct' : group carrier)



section
local attribute Group.carrier [coercion]
Definition pSet_of_Group [coercion] (G : Group) : Set*.
ptrunctype.mk (Group.carrier G) !semigroup.is_set_carrier 1
Defined.

Definition Group.struct [instance] [priority 2000] (G : Group) : group G.
Group.struct' G




Definition pType_of_Group (G : Group) : pType.
G
Definition Set_of_Group (G : Group) : Set.
G

Definition AddGroup : Type . Group

Definition pSet_of_AddGroup [coercion] (G : AddGroup) : Set*.
pSet_of_Group G

Definition AddGroup.mk (G : Type) (H : add_group G) : AddGroup.
Group.mk G H

Definition AddGroup.struct [instance] [priority 2000] (G : AddGroup) : add_group G.
Group.struct G




Definition pType_of_AddGroup : AddGroup -> pType.
algebra._trans_of_pSet_of_AddGroup_1
Definition Set_of_AddGroup : AddGroup -> Set.
algebra._trans_of_pSet_of_AddGroup_2

structure AbGroup.
(carrier : Type) (struct' : ab_group carrier)



section
local attribute AbGroup.carrier [coercion]
Definition Group_of_AbGroup [coercion] (G : AbGroup) : Group.
Group.mk G _
Defined.

Definition AbGroup.struct [instance] [priority 2000] (G : AbGroup) : ab_group G.
AbGroup.struct' G


  algebra._trans_of_Group_of_AbGroup
  algebra._trans_of_Group_of_AbGroup_3


Definition AddAbGroup : Type . AbGroup

Definition AddGroup_of_AddAbGroup [coercion] (G : AddAbGroup) : AddGroup.
Group_of_AbGroup G

Definition AddAbGroup.struct [instance] [priority 2000] (G : AddAbGroup) :
  add_ab_group G.
AbGroup.struct G

Definition AddAbGroup.mk (G : Type) (H : add_ab_group G) :
  AddAbGroup.
AbGroup.mk G H


  algebra._trans_of_AddGroup_of_AddAbGroup
  algebra._trans_of_AddGroup_of_AddAbGroup_3


(* structure AddSemigroup . *)
(* (carrier : Type) (struct : add_semigroup carrier) *)

(* attribute AddSemigroup.carrier [coercion] *)
(* attribute AddSemigroup.struct [instance] *)

(* structure AddCommSemigroup . *)
(* (carrier : Type) (struct : add_comm_semigroup carrier) *)

(* attribute AddCommSemigroup.carrier [coercion] *)
(* attribute AddCommSemigroup.struct [instance] *)

(* structure AddMonoid . *)
(* (carrier : Type) (struct : add_monoid carrier) *)

(* attribute AddMonoid.carrier [coercion] *)
(* attribute AddMonoid.struct [instance] *)

(* structure AddCommMonoid . *)
(* (carrier : Type) (struct : add_comm_monoid carrier) *)

(* attribute AddCommMonoid.carrier [coercion] *)
(* attribute AddCommMonoid.struct [instance] *)

(* structure AddGroup . *)
(* (carrier : Type) (struct : add_group carrier) *)

(* attribute AddGroup.carrier [coercion] *)
(* attribute AddGroup.struct [instance] *)

(* structure AddAbGroup . *)
(* (carrier : Type) (struct : add_ab_group carrier) *)

(* attribute AddAbGroup.carrier [coercion] *)
(* attribute AddAbGroup.struct [instance] *)


(* some bundled infinity-structures *)
structure InfGroup.
(carrier : Type) (struct' : inf_group carrier)



section
  local attribute InfGroup.carrier [coercion]
Definition pType_of_InfGroup [coercion] (G : InfGroup) : pType.
  Build_pType G 1
Defined.



Definition InfGroup.struct [instance] [priority 2000] (G : InfGroup) : inf_group G.
InfGroup.struct' G

Definition AddInfGroup : Type . InfGroup

Definition pType_of_AddInfGroup [coercion] (G : AddInfGroup) : pType.
pType_of_InfGroup G

Definition AddInfGroup.mk (G : Type) (H : add_inf_group G) :
  AddInfGroup.
InfGroup.mk G H

Definition AddInfGroup.struct (G : AddInfGroup) : add_inf_group G.
InfGroup.struct G



structure AbInfGroup.
(carrier : Type) (struct' : ab_inf_group carrier)



section
local attribute AbInfGroup.carrier [coercion]
Definition InfGroup_of_AbInfGroup [coercion] (G : AbInfGroup) : InfGroup.
InfGroup.mk G _
Defined.

Definition AbInfGroup.struct [instance] [priority 2000] (G : AbInfGroup) : ab_inf_group G.
AbInfGroup.struct' G




Definition AddAbInfGroup : Type . AbInfGroup

Definition AddInfGroup_of_AddAbInfGroup [coercion] (G : AddAbInfGroup) : AddInfGroup.
InfGroup_of_AbInfGroup G

Definition AddAbInfGroup.struct [instance] [priority 2000] (G : AddAbInfGroup) :
  add_ab_inf_group G.
AbInfGroup.struct G

Definition AddAbInfGroup.mk (G : Type) (H : add_ab_inf_group G) :
  AddAbInfGroup.
AbInfGroup.mk G H




Definition InfGroup_of_Group (G : Group) : InfGroup.
InfGroup.mk G _

Definition AddInfGroup_of_AddGroup (G : AddGroup) : AddInfGroup.
AddInfGroup.mk G _

Definition AbInfGroup_of_AbGroup (G : AbGroup) : AbInfGroup.
AbInfGroup.mk G _

Definition AddAbInfGroup_of_AddAbGroup (G : AddAbGroup) : AddAbInfGroup.
AddAbInfGroup.mk G _

(* rings *)
structure Ring.
(carrier : Type) (struct : ring carrier)




Defined. algebra
