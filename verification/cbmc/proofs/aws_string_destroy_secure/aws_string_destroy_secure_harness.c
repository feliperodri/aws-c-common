/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/string.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>

void aws_string_destroy_secure_harness() {
    /* Non-deterministic parameters. */
    struct aws_string *str = ensure_string_is_allocated_bounded_length(MAX_STRING_LEN);
    char const *bytes;
    size_t len;
    bool is_str_null = (str == NULL);

    /* Assumptions. */
    __CPROVER_assume(IMPLIES(str != NULL, aws_string_is_valid(str)));
    if (str != NULL) {
        bytes = str->bytes;
        len = str->len;
        is_str_null = false;
    }

    /* Operation under verification. */
    aws_string_destroy_secure(str);

    /* Check that all bytes are 0.  Since the memory is freed,
     * this will trigger a use-after-free check
     * Disabiling the check only for this bit of the harness. */
#pragma CPROVER check push
#pragma CPROVER check disable "pointer"
    if (!is_str_null) {
        if (len > 0) {
            size_t i;
            __CPROVER_assume(i < len);
            assert(bytes[i] == 0);
        }
    }
#pragma CPROVER check pop
}
