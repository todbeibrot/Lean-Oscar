// Lean compiler output
// Module: Mrdi.UUID
// Imports: Init Mathlib
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* l_instUUIDDecidableEq___boxed(lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Mrdi_UUID_0__UUID_add__minus(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
static lean_object* l_UUID_size___closed__1;
static lean_object* l_instUUIDFintype___closed__1;
LEAN_EXPORT lean_object* l_String_insertNth___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UUID_instReprUUID(lean_object*, lean_object*);
lean_object* l_String_Iterator_next(lean_object*);
lean_object* l_IO_rand(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parsec_unexpectedEndOfInput;
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Fin_ofNat(lean_object*, lean_object*);
lean_object* l_instDecidableEqFin___rarg___boxed(lean_object*, lean_object*);
uint32_t l_String_Iterator_curr(lean_object*);
lean_object* l_List_insertNthTR_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instOrdFin___rarg___boxed(lean_object*, lean_object*);
lean_object* lean_string_data(lean_object*);
static lean_object* l_UUID_parse___closed__1;
LEAN_EXPORT lean_object* l_UUID_parse(lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
static lean_object* l_UUID_instOfNatUUID___closed__1;
uint8_t l_String_Iterator_hasNext(lean_object*);
lean_object* l_List_range(lean_object*);
LEAN_EXPORT lean_object* l_UUID_instOfNatUUID(lean_object*);
lean_object* lean_string_mk(lean_object*);
LEAN_EXPORT lean_object* l_instUUIDToExpr;
static lean_object* l_String_insertNth___closed__1;
LEAN_EXPORT lean_object* l_UUID_instToFormatUUID(lean_object*);
LEAN_EXPORT lean_object* l_instUUIDFintype;
LEAN_EXPORT lean_object* l_UUID_hex__repr(lean_object*);
static lean_object* l_instUUIDBEq___closed__2;
static lean_object* l_instUUIDToExpr___closed__1;
LEAN_EXPORT lean_object* l_UUID_getUUID(lean_object*);
LEAN_EXPORT lean_object* l_UUID_repr(lean_object*);
LEAN_EXPORT uint8_t l_instUUIDDecidableEq(lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
LEAN_EXPORT lean_object* l_UUID_instToStringUUID(lean_object*);
LEAN_EXPORT lean_object* l_instUUIDBEq;
lean_object* l_Nat_toDigits(lean_object*, lean_object*);
static lean_object* l_instUUIDOrd___closed__1;
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_UUID_instReprUUID___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Mrdi_UUID_0__UUID_fill__with__zeros(lean_object*);
LEAN_EXPORT lean_object* l_instUUIDInhabited;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UUID_instOfNatUUID___boxed(lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l_instUUIDBEq___closed__1;
LEAN_EXPORT lean_object* l_UUID_UUIDCore(lean_object*, lean_object*, lean_object*);
static lean_object* l_UUID_parse___closed__3;
LEAN_EXPORT lean_object* l_instUUIDLT;
LEAN_EXPORT lean_object* l_List_mapM_loop___at_UUID_IO_randUUIDs___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UUID_size;
LEAN_EXPORT lean_object* l_instUUIDOrd;
lean_object* l_Fin_toExpr(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* l_instBEq___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UUID_IO_randUUID(lean_object*);
LEAN_EXPORT lean_object* l_UUID_UUIDCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_insertNth(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_UUID_IO_randUUIDs(lean_object*, lean_object*);
static lean_object* l_UUID_UUIDCore___lambda__1___closed__1;
lean_object* l_Nat_repr(lean_object*);
static lean_object* l_UUID_parse___closed__2;
static lean_object* _init_l_String_insertNth___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_insertNth(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_string_data(x_1);
x_5 = l_String_insertNth___closed__1;
x_6 = lean_box_uint32(x_2);
x_7 = l_List_insertNthTR_go___rarg(x_6, x_3, x_4, x_5);
x_8 = lean_string_mk(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_String_insertNth___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_String_insertNth(x_1, x_4, x_3);
return x_5;
}
}
static lean_object* _init_l_UUID_size___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_cstr_to_nat("340282366920938463463374607431768211456");
return x_1;
}
}
static lean_object* _init_l_UUID_size() {
_start:
{
lean_object* x_1; 
x_1 = l_UUID_size___closed__1;
return x_1;
}
}
static lean_object* _init_l_instUUIDInhabited() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
LEAN_EXPORT uint8_t l_instUUIDDecidableEq(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instUUIDDecidableEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_instUUIDDecidableEq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_instUUIDToExpr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_UUID_size___closed__1;
x_2 = l_Fin_toExpr(x_1);
return x_2;
}
}
static lean_object* _init_l_instUUIDToExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_instUUIDToExpr___closed__1;
return x_1;
}
}
static lean_object* _init_l_instUUIDFintype___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_UUID_size___closed__1;
x_2 = l_List_finRange(x_1);
return x_2;
}
}
static lean_object* _init_l_instUUIDFintype() {
_start:
{
lean_object* x_1; 
x_1 = l_instUUIDFintype___closed__1;
return x_1;
}
}
static lean_object* _init_l_instUUIDBEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqFin___rarg___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instUUIDBEq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instUUIDBEq___closed__1;
x_2 = lean_alloc_closure((void*)(l_instBEq___rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_instUUIDBEq() {
_start:
{
lean_object* x_1; 
x_1 = l_instUUIDBEq___closed__2;
return x_1;
}
}
static lean_object* _init_l_instUUIDLT() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_instUUIDOrd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instOrdFin___rarg___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instUUIDOrd() {
_start:
{
lean_object* x_1; 
x_1 = l_instUUIDOrd___closed__1;
return x_1;
}
}
static lean_object* _init_l_UUID_instOfNatUUID___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_cstr_to_nat("340282366920938463463374607431768211455");
return x_1;
}
}
LEAN_EXPORT lean_object* l_UUID_instOfNatUUID(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_UUID_instOfNatUUID___closed__1;
x_3 = l_Fin_ofNat(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_UUID_instOfNatUUID___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_UUID_instOfNatUUID(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Mrdi_UUID_0__UUID_fill__with__zeros(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_string_length(x_1);
x_3 = lean_unsigned_to_nat(32u);
x_4 = lean_nat_dec_lt(x_2, x_3);
lean_dec(x_2);
if (x_4 == 0)
{
return x_1;
}
else
{
uint32_t x_5; lean_object* x_6; 
x_5 = 48;
x_6 = lean_string_push(x_1, x_5);
x_1 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Mrdi_UUID_0__UUID_add__minus(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = 45;
x_3 = lean_unsigned_to_nat(8u);
x_4 = l_String_insertNth(x_1, x_2, x_3);
x_5 = lean_unsigned_to_nat(13u);
x_6 = l_String_insertNth(x_4, x_2, x_5);
x_7 = lean_unsigned_to_nat(18u);
x_8 = l_String_insertNth(x_6, x_2, x_7);
x_9 = lean_unsigned_to_nat(23u);
x_10 = l_String_insertNth(x_8, x_2, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_UUID_hex__repr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(16u);
x_3 = l_Nat_toDigits(x_2, x_1);
x_4 = lean_string_mk(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_UUID_repr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_UUID_hex__repr(x_1);
x_3 = l___private_Mrdi_UUID_0__UUID_fill__with__zeros(x_2);
x_4 = l___private_Mrdi_UUID_0__UUID_add__minus(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_UUID_instReprUUID(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_UUID_repr(x_1);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_UUID_instReprUUID___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_UUID_instReprUUID(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_UUID_instToStringUUID(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_UUID_repr(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_UUID_instToFormatUUID(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_UUID_repr(x_1);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_UUID_UUIDCore___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid hex character", 21);
return x_1;
}
}
LEAN_EXPORT lean_object* l_UUID_UUIDCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = l_String_Iterator_hasNext(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = l_Lean_Parsec_unexpectedEndOfInput;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; uint32_t x_9; lean_object* x_10; lean_object* x_31; uint32_t x_50; uint8_t x_51; 
lean_inc(x_4);
x_8 = l_String_Iterator_next(x_4);
x_9 = l_String_Iterator_curr(x_4);
lean_dec(x_4);
x_50 = 48;
x_51 = lean_uint32_dec_le(x_50, x_9);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_box(0);
x_31 = x_52;
goto block_49;
}
else
{
uint32_t x_53; uint8_t x_54; 
x_53 = 57;
x_54 = lean_uint32_dec_le(x_9, x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_box(0);
x_31 = x_55;
goto block_49;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_56 = lean_uint32_to_nat(x_9);
x_57 = lean_unsigned_to_nat(48u);
x_58 = lean_nat_sub(x_56, x_57);
lean_dec(x_56);
x_59 = lean_unsigned_to_nat(16u);
x_60 = lean_nat_mul(x_59, x_1);
lean_dec(x_1);
x_61 = lean_nat_add(x_60, x_58);
lean_dec(x_58);
lean_dec(x_60);
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_nat_add(x_2, x_62);
lean_dec(x_2);
x_64 = l_UUID_UUIDCore(x_61, x_63, x_8);
return x_64;
}
}
block_30:
{
uint32_t x_11; uint8_t x_12; 
lean_dec(x_10);
x_11 = 65;
x_12 = lean_uint32_dec_le(x_11, x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_UUID_UUIDCore___lambda__1___closed__1;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
uint32_t x_15; uint8_t x_16; 
x_15 = 70;
x_16 = lean_uint32_dec_le(x_9, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_17 = l_UUID_UUIDCore___lambda__1___closed__1;
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_uint32_to_nat(x_9);
x_20 = lean_unsigned_to_nat(65u);
x_21 = lean_nat_sub(x_19, x_20);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(10u);
x_23 = lean_nat_add(x_21, x_22);
lean_dec(x_21);
x_24 = lean_unsigned_to_nat(16u);
x_25 = lean_nat_mul(x_24, x_1);
lean_dec(x_1);
x_26 = lean_nat_add(x_25, x_23);
lean_dec(x_23);
lean_dec(x_25);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_2, x_27);
lean_dec(x_2);
x_29 = l_UUID_UUIDCore(x_26, x_28, x_8);
return x_29;
}
}
}
block_49:
{
uint32_t x_32; uint8_t x_33; 
lean_dec(x_31);
x_32 = 97;
x_33 = lean_uint32_dec_le(x_32, x_9);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_box(0);
x_10 = x_34;
goto block_30;
}
else
{
uint32_t x_35; uint8_t x_36; 
x_35 = 102;
x_36 = lean_uint32_dec_le(x_9, x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_box(0);
x_10 = x_37;
goto block_30;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_38 = lean_uint32_to_nat(x_9);
x_39 = lean_unsigned_to_nat(97u);
x_40 = lean_nat_sub(x_38, x_39);
lean_dec(x_38);
x_41 = lean_unsigned_to_nat(10u);
x_42 = lean_nat_add(x_40, x_41);
lean_dec(x_40);
x_43 = lean_unsigned_to_nat(16u);
x_44 = lean_nat_mul(x_43, x_1);
lean_dec(x_1);
x_45 = lean_nat_add(x_44, x_42);
lean_dec(x_42);
lean_dec(x_44);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_add(x_2, x_46);
lean_dec(x_2);
x_48 = l_UUID_UUIDCore(x_45, x_47, x_8);
return x_48;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_UUID_UUIDCore(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_18; 
x_18 = l_String_Iterator_hasNext(x_3);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_box(0);
x_4 = x_3;
x_5 = x_19;
goto block_17;
}
else
{
uint32_t x_20; lean_object* x_21; lean_object* x_22; 
x_20 = l_String_Iterator_curr(x_3);
x_21 = lean_box_uint32(x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_4 = x_3;
x_5 = x_22;
goto block_17;
}
block_17:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; uint32_t x_9; uint32_t x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = 45;
x_10 = lean_unbox_uint32(x_8);
lean_dec(x_8);
x_11 = lean_uint32_dec_eq(x_10, x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = l_UUID_UUIDCore___lambda__1(x_1, x_2, x_12, x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_String_Iterator_next(x_4);
x_15 = lean_box(0);
x_16 = l_UUID_UUIDCore___lambda__1(x_1, x_2, x_15, x_14);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_UUID_getUUID(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_UUID_UUIDCore(x_2, x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
static lean_object* _init_l_UUID_parse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("offset ", 7);
return x_1;
}
}
static lean_object* _init_l_UUID_parse___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": ", 2);
return x_1;
}
}
static lean_object* _init_l_UUID_parse___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_UUID_parse(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
x_4 = l_UUID_getUUID(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_UUID_instOfNatUUID___closed__1;
x_7 = l_Fin_ofNat(x_6, x_5);
lean_dec(x_5);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Nat_repr(x_11);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Std_Format_defWidth;
x_15 = lean_format_pretty(x_13, x_14, x_2, x_2);
x_16 = l_UUID_parse___closed__1;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_UUID_parse___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_string_append(x_19, x_10);
lean_dec(x_10);
x_21 = l_UUID_parse___closed__3;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_UUID_IO_randUUID(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_UUID_size;
x_4 = l_IO_rand(x_2, x_3, x_1);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_UUID_instOfNatUUID___closed__1;
x_8 = l_Fin_ofNat(x_7, x_6);
lean_dec(x_6);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = l_UUID_instOfNatUUID___closed__1;
x_12 = l_Fin_ofNat(x_11, x_9);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_UUID_IO_randUUIDs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_List_reverse___rarg(x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 0);
lean_dec(x_8);
x_9 = l_UUID_IO_randUUID(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_10);
{
lean_object* _tmp_0 = x_7;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_2 = x_11;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l_UUID_IO_randUUID(x_3);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_2);
x_1 = x_13;
x_2 = x_17;
x_3 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_UUID_IO_randUUIDs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_List_range(x_1);
x_4 = lean_box(0);
x_5 = l_List_mapM_loop___at_UUID_IO_randUUIDs___spec__1(x_3, x_4, x_2);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Mrdi_UUID(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_String_insertNth___closed__1 = _init_l_String_insertNth___closed__1();
lean_mark_persistent(l_String_insertNth___closed__1);
l_UUID_size___closed__1 = _init_l_UUID_size___closed__1();
lean_mark_persistent(l_UUID_size___closed__1);
l_UUID_size = _init_l_UUID_size();
lean_mark_persistent(l_UUID_size);
l_instUUIDInhabited = _init_l_instUUIDInhabited();
lean_mark_persistent(l_instUUIDInhabited);
l_instUUIDToExpr___closed__1 = _init_l_instUUIDToExpr___closed__1();
lean_mark_persistent(l_instUUIDToExpr___closed__1);
l_instUUIDToExpr = _init_l_instUUIDToExpr();
lean_mark_persistent(l_instUUIDToExpr);
l_instUUIDFintype___closed__1 = _init_l_instUUIDFintype___closed__1();
lean_mark_persistent(l_instUUIDFintype___closed__1);
l_instUUIDFintype = _init_l_instUUIDFintype();
lean_mark_persistent(l_instUUIDFintype);
l_instUUIDBEq___closed__1 = _init_l_instUUIDBEq___closed__1();
lean_mark_persistent(l_instUUIDBEq___closed__1);
l_instUUIDBEq___closed__2 = _init_l_instUUIDBEq___closed__2();
lean_mark_persistent(l_instUUIDBEq___closed__2);
l_instUUIDBEq = _init_l_instUUIDBEq();
lean_mark_persistent(l_instUUIDBEq);
l_instUUIDLT = _init_l_instUUIDLT();
lean_mark_persistent(l_instUUIDLT);
l_instUUIDOrd___closed__1 = _init_l_instUUIDOrd___closed__1();
lean_mark_persistent(l_instUUIDOrd___closed__1);
l_instUUIDOrd = _init_l_instUUIDOrd();
lean_mark_persistent(l_instUUIDOrd);
l_UUID_instOfNatUUID___closed__1 = _init_l_UUID_instOfNatUUID___closed__1();
lean_mark_persistent(l_UUID_instOfNatUUID___closed__1);
l_UUID_UUIDCore___lambda__1___closed__1 = _init_l_UUID_UUIDCore___lambda__1___closed__1();
lean_mark_persistent(l_UUID_UUIDCore___lambda__1___closed__1);
l_UUID_parse___closed__1 = _init_l_UUID_parse___closed__1();
lean_mark_persistent(l_UUID_parse___closed__1);
l_UUID_parse___closed__2 = _init_l_UUID_parse___closed__2();
lean_mark_persistent(l_UUID_parse___closed__2);
l_UUID_parse___closed__3 = _init_l_UUID_parse___closed__3();
lean_mark_persistent(l_UUID_parse___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
