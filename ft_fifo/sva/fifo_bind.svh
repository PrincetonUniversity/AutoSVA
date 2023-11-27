bind fifo fifo_prop
	#(
		.INFLIGHT_IDX (INFLIGHT_IDX),
		.SIZE (SIZE),
		.ASSERT_INPUTS (0)
	) u_fifo_sva(.*);