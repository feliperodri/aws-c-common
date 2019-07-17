/*
 * Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

#include <aws/common/encoding.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>

void aws_hex_encode_harness() {
    /* parameters */
    struct aws_byte_cursor to_encode;
    struct aws_byte_buf output;

    /* assumptions */
    __CPROVER_assume(aws_byte_cursor_is_bounded(&to_encode, MAX_BUFFER_SIZE));
    ensure_byte_cursor_has_allocated_buffer_member(&to_encode);
    __CPROVER_assume(aws_byte_cursor_is_valid(&to_encode));
    __CPROVER_assume(aws_byte_buf_is_bounded(&output, MAX_BUFFER_SIZE));
    ensure_byte_buf_has_allocated_buffer_member(&output);
    __CPROVER_assume(aws_byte_buf_is_valid(&output));

    /* save current state of the data structure */
    struct aws_byte_cursor old_to_encode = to_encode;
    struct store_byte_from_buffer old_byte_from_to_encode;
    save_byte_from_array(to_encode.ptr, to_encode.len, &old_byte_from_to_encode);
    struct aws_byte_buf old_output = output;
    struct store_byte_from_buffer old_byte_from_output;
    save_byte_from_array(output.buffer, output.len, &old_byte_from_output);

    /* operation under verification */
    if (aws_hex_encode(&to_encode, &output) != AWS_OP_SUCCESS && output.len > 0) {
          assert_byte_buf_equivalence(&output, &old_output, &old_byte_from_output);
    }

    /* assertions */
    assert(aws_byte_cursor_is_valid(&to_encode));
    assert(aws_byte_buf_is_valid(&output));
    if (to_encode.len > 0) {
        assert_byte_cursor_equivalence(&to_encode, &old_to_encode, &old_byte_from_to_encode);
    }
}
