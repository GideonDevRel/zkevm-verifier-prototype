// Lean compiler output
// Module: zkEVM.EVMMulMod
// Imports: Init
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
LEAN_EXPORT lean_object* l_nat__to__word256(lean_object*);
LEAN_EXPORT lean_object* l_nat__to__word256___boxed(lean_object*);
static lean_object* l_stack__effect__add___closed__2;
LEAN_EXPORT lean_object* l_evm__mulmod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_evm__mulmod___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WORD__ZERO;
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_evm__mulmod__gas__cost;
LEAN_EXPORT lean_object* l_stack__effect__add;
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
static lean_object* l_stack__effect__add___closed__1;
lean_object* lean_int_neg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_evm__mulmod___closed__1;
static lean_object* _init_l_evm__mulmod___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_unsigned_to_nat(256u);
x_3 = lean_nat_pow(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_evm__mulmod(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_nat_add(x_1, x_2);
x_4 = l_evm__mulmod___closed__1;
x_5 = lean_nat_mod(x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_evm__mulmod___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_evm__mulmod(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_nat__to__word256(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_evm__mulmod___closed__1;
x_3 = lean_nat_mod(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_nat__to__word256___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_nat__to__word256(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_WORD__ZERO() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_evm__mulmod__gas__cost() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(3u);
return x_1;
}
}
static lean_object* _init_l_stack__effect__add___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_stack__effect__add___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_stack__effect__add___closed__1;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_stack__effect__add() {
_start:
{
lean_object* x_1; 
x_1 = l_stack__effect__add___closed__2;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_zkEVM_EVMMulMod(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_evm__mulmod___closed__1 = _init_l_evm__mulmod___closed__1();
lean_mark_persistent(l_evm__mulmod___closed__1);
l_WORD__ZERO = _init_l_WORD__ZERO();
lean_mark_persistent(l_WORD__ZERO);
l_evm__mulmod__gas__cost = _init_l_evm__mulmod__gas__cost();
lean_mark_persistent(l_evm__mulmod__gas__cost);
l_stack__effect__add___closed__1 = _init_l_stack__effect__add___closed__1();
lean_mark_persistent(l_stack__effect__add___closed__1);
l_stack__effect__add___closed__2 = _init_l_stack__effect__add___closed__2();
lean_mark_persistent(l_stack__effect__add___closed__2);
l_stack__effect__add = _init_l_stack__effect__add();
lean_mark_persistent(l_stack__effect__add);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
