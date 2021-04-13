#ifndef SIM_OO_H_
#define SIM_OO_H_

#include <stdio.h>
#include <stdbool.h>
#include <string>
#include <cstring>
#include <sstream>

using namespace std;

#define UNDEFINED 0xFFFFFFFF //constant used for initialization
#define NUM_GP_REGISTERS 32
#define NUM_OPCODES 24
#define NUM_STAGES 4
#define MAX_UNITS 10
#define PROGRAM_SIZE 50

// instructions supported
typedef enum
{
	LW,
	SW,
	ADD,
	ADDI,
	SUB,
	SUBI,
	XOR,
	AND,
	MULT,
	DIV,
	BEQZ,
	BNEZ,
	BLTZ,
	BGTZ,
	BLEZ,
	BGEZ,
	JUMP,
	EOP,
	LWS,
	SWS,
	ADDS,
	SUBS,
	MULTS,
	DIVS
} opcode_t;

// reservation stations types
typedef enum
{
	INTEGER_RS,
	ADD_RS,
	MULT_RS,
	LOAD_B
} res_station_t;

// execution units types
typedef enum
{
	INTEGER,
	ADDER,
	MULTIPLIER,
	DIVIDER,
	MEMORY
} exe_unit_t;

// stages names
typedef enum
{
	ISSUE,
	EXECUTE,
	WRITE_RESULT,
	COMMIT
} stage_t;

// instruction data type
typedef struct
{
	opcode_t opcode;	//opcode
	unsigned src1;		//first source register in the assembly instruction (for SW, register to be written to memory)
	unsigned src2;		//second source register in the assembly instruction
	unsigned dest;		//destination register
	unsigned immediate; //immediate field
	string label;		//for conditional branches, label of the target instruction - used only for parsing/debugging purposes
} instruction_t;

// execution unit
typedef struct
{
	exe_unit_t type;  // execution unit type
	unsigned latency; // execution unit latency
	unsigned busy;	  // 0 if execution unit is free, otherwise number of clock cycles during
					  // which the execution unit will be busy. It should be initialized
					  // to the latency of the unit when the unit becomes busy, and decremented
					  // at each clock cycle
	unsigned pc;	  // PC of the instruction using the functional unit
	unsigned ALUoutput;
} unit_t;

// entry in the "instruction window"
typedef struct
{
	unsigned pc;	 // PC of the instruction
	unsigned issue;	 // clock cycle when the instruction is issued
	unsigned exe;	 // clock cycle when the instruction enters execution
	unsigned wr;	 // clock cycle when the instruction enters write result
	unsigned commit; // clock cycle when the instruction commits (for stores, clock cycle when the store starts committing
} instr_window_entry_t;

// ROB entry
typedef struct
{
	bool ready;			  // ready field
	unsigned pc;		  // pc of corresponding instruction (set to UNDEFINED if ROB entry is available)
	stage_t state;		  // state field
	unsigned destination; // destination field
	unsigned value;		  // value field
	bool store_bypassed;  //I added this field
} rob_entry_t;

// reservation station entry
typedef struct
{
	res_station_t type;	  // reservation station type
	unsigned name;		  // reservation station name (i.e., "Int", "Add", "Mult", "Load") for logging purposes
	unsigned pc;		  // pc of corresponding instruction (set to UNDEFINED if reservation station is available)
	unsigned value1;	  // Vj field
	unsigned value2;	  // Vk field
	unsigned tag1;		  // Qj field
	unsigned tag2;		  // Qk field
	unsigned destination; // destination field
	unsigned address;	  // address field (for loads and stores)
} res_station_entry_t;

//instruction window
typedef struct
{
	unsigned num_entries;
	instr_window_entry_t *entries;
} instr_window_t;

// ROB
typedef struct
{
	unsigned num_entries;
	rob_entry_t *entries;
} rob_t;

// reservation stations
typedef struct
{
	unsigned num_entries;
	res_station_entry_t *entries;
} res_stations_t;

class sim_ooo
{

	/* Add the data members required by your simulator's implementation here */

	/* end added data members */

	//issue width
	unsigned issue_width;

	//instruction window
	instr_window_t pending_instructions;

	//reorder buffer
	rob_t rob;

	//reservation stations
	res_stations_t reservation_stations;

	//execution units
	unit_t exec_units[MAX_UNITS];
	unsigned num_units;

	//instruction memory
	instruction_t instr_memory[PROGRAM_SIZE];

	//base address in the instruction memory where the program is loaded
	unsigned instr_base_address;

	//data memory - should be initialize to all 0xFF
	unsigned char *data_memory;

	//memory size in bytes
	unsigned data_memory_size;

	//instruction executed
	unsigned instructions_executed;

	//clock cycles
	unsigned clock_cycles;

	//execution log
	stringstream log;

public:
	/* Instantiates the simulator
          	Note: registers must be initialized to UNDEFINED value, and data memory to all 0xFF values
        */
	sim_ooo(unsigned mem_size,			   // size of data memory (in byte)
			unsigned rob_size,			   // number of ROB entries
			unsigned num_int_res_stations, // number of integer reservation stations
			unsigned num_add_res_stations, // number of ADD reservation stations
			unsigned num_mul_res_stations, // number of MULT/DIV reservation stations
			unsigned num_load_buffers,	   // number of LOAD buffers
			unsigned issue_width = 1	   // issue width
	);

	//de-allocates the simulator
	~sim_ooo();

	// adds one or more execution units of a given type to the processor
	// - exec_unit: type of execution unit to be added
	// - latency: latency of the execution unit (in clock cycles)
	// - instances: number of execution units of this type to be added
	void init_exec_unit(exe_unit_t exec_unit, unsigned latency, unsigned instances = 1);

	//related to functional unit
	unsigned get_free_unit(opcode_t opcode);

	//taken from project 1
	void decrement_units_busy_time();
	void debug_units();

	//loads the assembly program in file "filename" in instruction memory at the specified address
	void load_program(const char *filename, unsigned base_address = 0x0);

	//runs the simulator for "cycles" clock cycles (run the program to completion if cycles=0)
	void run(unsigned cycles = 0);

	//resets the state of the simulator
	/* Note: 
	   - registers should be reset to UNDEFINED value 
	   - data memory should be reset to all 0xFF values
	   - instruction window, reservation stations and rob should be cleaned
	*/
	void reset();

	//returns value of the specified integer general purpose register
	int get_int_register(unsigned reg);

	//set the value of the given integer general purpose register to "value"
	void set_int_register(unsigned reg, int value);

	//returns value of the specified floating point general purpose register
	float get_fp_register(unsigned reg);

	//set the value of the given floating point general purpose register to "value"
	void set_fp_register(unsigned reg, float value);

	// returns the index of the ROB entry that will write this integer register (UNDEFINED if the value of the register is not pending
	unsigned get_int_register_tag(unsigned reg);

	// returns the index of the ROB entry that will write this floating point register (UNDEFINED if the value of the register is not pending
	unsigned get_fp_register_tag(unsigned reg);

	//returns the IPC
	float get_IPC();

	//returns the number of instructions fully executed
	unsigned get_instructions_executed();

	//returns the number of clock cycles
	unsigned get_clock_cycles();

	//prints the content of the data memory within the specified address range
	void print_memory(unsigned start_address, unsigned end_address);

	// writes an integer value to data memory at the specified address (use little-endian format: https://en.wikipedia.org/wiki/Endianness)
	void write_memory(unsigned address, unsigned value);

	//prints the values of the registers
	void print_registers();

	//prints the status of processor excluding memory
	void print_status();

	// prints the content of the ROB
	void print_rob();

	//prints the content of the reservation stations
	void print_reservation_stations();

	//print the content of the instruction window
	void print_pending_instructions();

	//initialize the execution log
	void init_log();

	//commit an instruction to the log
	void commit_to_log(instr_window_entry_t iwe);

	//print log
	void print_log();
};

#endif /*SIM_OOO_H_*/
