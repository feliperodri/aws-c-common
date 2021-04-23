/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/clock.h>
//#include <proof_helpers/make_common_data_structures.h>

void aws_timestamp_convert_harness() {
    /* Non-deterministic inputs. */
    uint64_t timestamp;
    enum aws_timestamp_unit convert_from;
    enum aws_timestamp_unit convert_to;
    uint64_t *remainder = malloc(sizeof(*remainder));

    /* Operation under verification. */
    uint64_t res = aws_timestamp_convert(timestamp, convert_from, convert_to, remainder);
}
