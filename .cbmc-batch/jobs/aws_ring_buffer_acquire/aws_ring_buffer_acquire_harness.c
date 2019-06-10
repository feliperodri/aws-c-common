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

#include <aws/common/byte_buf.h>
#include <aws/common/ring_buffer.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>

#define MAX(x, y) (((x) > (y)) ? (x) : (y))

void aws_ring_buffer_acquire_harness() {
    /* parameters */
    struct aws_ring_buffer ring_buf;
    size_t ring_buf_size;
    size_t requested_size;
    size_t available_size;
    struct aws_byte_buf buf;

    /* assumptions */
    ensure_ring_buffer_has_allocated_members(&ring_buf, ring_buf_size);
    __CPROVER_assume(aws_ring_buffer_is_valid(&ring_buf));
    ensure_byte_buf_has_allocated_buffer_member(&buf);
    __CPROVER_assume(aws_byte_buf_is_valid(&buf));

    if(ring_buf.head == ring_buf.tail) {
        available_size = ring_buf_size;
    } else if (ring_buf.tail > ring_buf.head) {
        available_size = ring_buf.tail - ring_buf.head;
    } else if (ring_buf.tail < ring_buf.head) {
        available_size = MAX(ring_buf.allocation_end - ring_buf.head, ring_buf.tail - ring_buf.allocation);
    }
    if (aws_ring_buffer_acquire(nondet_bool() ? &ring_buf : NULL, requested_size, nondet_bool() ? &buf : NULL) ==
        AWS_OP_SUCCESS) {
        /* assertions */
        assert(available_size >= requested_size);
        assert(aws_ring_buffer_is_valid(&ring_buf));
        assert(aws_byte_buf_is_valid(&buf));
        assert(AWS_MEM_IS_WRITABLE(buf.buffer, requested_size));
        assert(buf.capacity == requested_size);
        assert(buf.len == 0); /* aws_byte_buf always created with aws_byte_buf_from_empty_array */
        assert(buf.buffer >= ring_buf.allocation && (buf.buffer + buf.capacity) <= (ring_buf.allocation_end));
    } else {
        if (aws_last_error() == AWS_ERROR_OOM) {
            assert(available_size < requested_size);
        }
    }
}
