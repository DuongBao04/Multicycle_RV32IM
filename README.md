# Multicycle_RV32IM
1\. Multi-Cycle Datapath
------------------------

A multi-cycle microarchitecture executes each instruction in several shorter cycles. Complex instructions use more cycles, while simpler ones use fewer. Hardware resources such as adders and memory are reused across cycles, reducing total hardware cost.

To support this microarchitecture, the processor introduces internal registers to store intermediate values. Only one instruction is active at a time, but each progresses through multiple cycles. A single memory unit is shared for both instruction fetch and data access in different cycles.

This design is adapted from the original single-cycle datapath (homework #3) and modified to support multi-cycle execution.

2\. Pipelined Divider (8 Stages)
--------------------------------

The divider is redesigned to break the critical path into 8 pipeline stages.Key properties:

*   Each stage performs **four iterations** of the division algorithm.
    
*   The divider supports **throughput of one new input per clock cycle**.
    
*   Latency is fixed at **8 cycles** per division.
    
*   The pipeline structure improves maximum clock frequency at the cost of additional latency.
    

Although the divider allows issuing a new divide every cycle, the current datapath uses it conservatively: each divide instruction (div, divu, rem, remu) still occupies the divider for 8 full cycles.

3\. Datapath Integration
------------------------

The divider is integrated into the multi-cycle datapath with minimal structural changes:

*   New control logic ensures divide instructions take exactly 8 cycles.
    
*   The existing CLA (Carry Lookahead Adder) from homework #2 remains part of the arithmetic logic.
    
*   The processor executes all non-divide instructions normally while handling divide instructions with dedicated multi-cycle control.
    

If multiple divide instructions appear consecutively, the datapath handles them sequentially:k divide instructions require 8k cycles.
