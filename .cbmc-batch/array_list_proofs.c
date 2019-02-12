#include <aws/common/array_list.h>
#include <assert.h>
#include <stddef.h>
#include <string.h>
#include <stdlib.h>
#include <stdarg.h>
#include <proof_helpers.h>

void aws_array_list_init_dynamic_verify(void) {
    struct aws_array_list *list;
    ASSUME_VALID_MEMORY(list);
    struct aws_allocator *allocator;
    ASSUME_DEFAULT_ALLOCATOR(allocator);
    size_t item_count = nondet_size_t();
    size_t item_size = nondet_size_t();

    aws_array_list_init_dynamic(list, allocator, item_count, item_size);

    /* some guarantees */
    assert(list->alloc == allocator);
    assert(list->item_size == item_size);
    if (item_count <= MAX_INITIAL_ITEM_ALLOCATION && item_size <= MAX_ITEM_SIZE)
        assert(list->data == NULL || list->current_size == (item_count * item_size));
}

void aws_array_list_init_static_verify(void) {
    struct aws_array_list *list;
    ASSUME_VALID_MEMORY(list);
    size_t len = nondet_size_t();
    void *raw_array = malloc(len);
    size_t item_count = nondet_size_t();
    __CPROVER_assume(item_count > 0);
    size_t item_size = nondet_size_t();
    __CPROVER_assume(item_size > 0);


    aws_array_list_init_static(list, raw_array, item_count, item_size);

    /* some guarantees */
    assert(list->alloc == NULL);
    assert(list->item_size == item_size);
    assert(list->data == raw_array);
}

void aws_array_list_set_at_verify(void) {
    size_t item_count = nondet_size_t();
    __CPROVER_assume(item_count <= MAX_INITIAL_ITEM_ALLOCATION);
    size_t item_size = nondet_size_t();
    __CPROVER_assume(item_size <= MAX_ITEM_SIZE);
    struct aws_array_list *list;
    ASSUME_ARBITRARY_ARRAY_LIST(list, item_count, item_size);

    void *val = malloc(item_size);

    size_t index = nondet_size_t();
    __CPROVER_assume(index < __CPROVER_constant_infinity_uint - 1);

    aws_array_list_set_at(list, val, index);
}

void aws_array_list_push_back_verify(void) {
    size_t item_count = nondet_size_t();
    __CPROVER_assume(item_count <= MAX_INITIAL_ITEM_ALLOCATION);
    size_t item_size = nondet_size_t();
    __CPROVER_assume(item_size <= MAX_ITEM_SIZE);
    struct aws_array_list *list;
    ASSUME_ARBITRARY_ARRAY_LIST(list, item_count, item_size);

    size_t len = list->length;
    void *val = malloc(item_size);

    aws_array_list_push_back(list, val);

    /* some guarantees */
    assert(list->length == len + 1);
}

void aws_array_list_back_verify(void) {
    size_t item_count = nondet_size_t();
    __CPROVER_assume(item_count <= MAX_INITIAL_ITEM_ALLOCATION);
    size_t item_size = nondet_size_t();
    __CPROVER_assume(item_size <= MAX_ITEM_SIZE);
    struct aws_array_list *list;
    ASSUME_ARBITRARY_ARRAY_LIST(list, item_count, item_size);

    void *val = malloc(item_size);

    aws_array_list_back(list, val);
}

void aws_array_list_clean_up_verify(void) {
    size_t item_count = nondet_size_t();
    __CPROVER_assume(item_count <= MAX_INITIAL_ITEM_ALLOCATION);
    size_t item_size = nondet_size_t();
    __CPROVER_assume(item_size <= MAX_ITEM_SIZE);
    struct aws_array_list *list;
    ASSUME_ARBITRARY_ARRAY_LIST(list, item_count, item_size);

    aws_array_list_clean_up(list);

    /* some guarantees */
    assert(list->length == 0);
    assert(list->alloc == NULL);
    assert(list->current_size == 0);
    assert(list->item_size == 0);
    assert(list->data == NULL);
}

void aws_array_list_clear_verify(void) {
    size_t item_count = nondet_size_t();
    __CPROVER_assume(item_count <= MAX_INITIAL_ITEM_ALLOCATION);
    size_t item_size = nondet_size_t();
    __CPROVER_assume(item_size <= MAX_ITEM_SIZE);
    struct aws_array_list *list;
    ASSUME_ARBITRARY_ARRAY_LIST(list, item_count, item_size);

    size_t prev_current_size = list->current_size;
    size_t prev_item_size = list->item_size;
    void* prev_data = list->data;

    aws_array_list_clear(list);

    /* some guarantees */
    assert(list->length == 0);
    assert(list->current_size == prev_current_size);
    assert(list->item_size == prev_item_size);
    assert(list->data == prev_data);
}

void aws_array_list_front_verify(void) {
    size_t item_count = nondet_size_t();
    __CPROVER_assume(item_count <= MAX_INITIAL_ITEM_ALLOCATION);
    size_t item_size = nondet_size_t();
    __CPROVER_assume(item_size <= MAX_ITEM_SIZE);
    struct aws_array_list *list;
    ASSUME_ARBITRARY_ARRAY_LIST(list, item_count, item_size);

    void *val = malloc(item_size);

    aws_array_list_front(list, val);
}

void aws_array_list_get_at_verify(void) {
    size_t item_count = nondet_size_t();
    __CPROVER_assume(item_count <= MAX_INITIAL_ITEM_ALLOCATION);
    size_t item_size = nondet_size_t();
    __CPROVER_assume(item_size <= MAX_ITEM_SIZE);
    struct aws_array_list *list;
    ASSUME_ARBITRARY_ARRAY_LIST(list, item_count, item_size);

    void *val = malloc(item_size);

    size_t index = nondet_size_t();
    __CPROVER_assume(index < __CPROVER_constant_infinity_uint - 1);
    __CPROVER_assume(list->length > index);

    aws_array_list_get_at(list, val, index);
}

void aws_array_list_get_at_ptr_verify(void) {
    size_t item_count = nondet_size_t();
    __CPROVER_assume(item_count <= MAX_INITIAL_ITEM_ALLOCATION);
    size_t item_size = nondet_size_t();
    __CPROVER_assume(item_size <= MAX_ITEM_SIZE);
    struct aws_array_list *list;
    ASSUME_ARBITRARY_ARRAY_LIST(list, item_count, item_size);

    void *val = malloc(item_size);

     size_t index = nondet_size_t();
    __CPROVER_assume(index < __CPROVER_constant_infinity_uint - 1);
    __CPROVER_assume(list->length > index);

    aws_array_list_get_at_ptr(list, &val, index);
}

void aws_array_list_length_verify(void) {
    size_t item_count = nondet_size_t();
    __CPROVER_assume(item_count <= MAX_INITIAL_ITEM_ALLOCATION);
    size_t item_size = nondet_size_t();
    __CPROVER_assume(item_size <= MAX_ITEM_SIZE);
    struct aws_array_list *list;
    ASSUME_ARBITRARY_ARRAY_LIST(list, item_count, item_size);

    size_t len = aws_array_list_length(list);

    assert(len == list->length);
}

void aws_array_list_swap_contents_verify(void) {
    size_t item_count_a = nondet_size_t();
    __CPROVER_assume(item_count_a <= MAX_INITIAL_ITEM_ALLOCATION);
    size_t item_size_a = nondet_size_t();
    __CPROVER_assume(item_size_a <= MAX_ITEM_SIZE);
    struct aws_array_list *list_a;
    ASSUME_ARBITRARY_ARRAY_LIST(list_a, item_count_a, item_size_a);

    size_t item_count_b = nondet_size_t();
    __CPROVER_assume(item_count_b <= MAX_INITIAL_ITEM_ALLOCATION);
    size_t item_size_b = nondet_size_t();
    __CPROVER_assume(item_size_b <= MAX_ITEM_SIZE);
    struct aws_array_list *list_b;
    ASSUME_ARBITRARY_ARRAY_LIST(list_b, item_count_b, item_size_b);

    __CPROVER_assume(list_a->alloc != NULL);
    __CPROVER_assume(list_a->alloc == list_b->alloc);
    __CPROVER_assume(list_a->item_size == list_b->item_size);
    __CPROVER_assume(list_a != list_b);

    aws_array_list_swap_contents(list_a, list_b);
}
