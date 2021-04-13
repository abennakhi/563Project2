#include "sim_ooo.h"
#include <stdlib.h>
#include <iostream>
#include <fstream>
#include <cstring>
#include <string>
#include <iomanip>
#include <map>

using namespace std;

//used for debugging purposes
static const char *stage_names[NUM_STAGES] = {"ISSUE", "EXE", "WR", "COMMIT"};
static const char *instr_names[NUM_OPCODES] = {"LW", "SW", "ADD", "ADDI", "SUB", "SUBI", "XOR", "AND", "MULT", "DIV", "BEQZ", "BNEZ", "BLTZ", "BGTZ", "BLEZ", "BGEZ", "JUMP", "EOP", "LWS", "SWS", "ADDS", "SUBS", "MULTS", "DIVS"};
static const char *res_station_names[5] = {"Int", "Add", "Mult", "Load"};

float FP_regs[NUM_GP_REGISTERS];
int INT_regs[NUM_GP_REGISTERS];
int PC;
int FP_tags[NUM_GP_REGISTERS];
int INT_tags[NUM_GP_REGISTERS];
int ROBindex4ResStations;
int ROBentryIndex;
bool vacantPlace;

//stall flags
bool issue_struct_stall;

/* =============================================================

   HELPER FUNCTIONS (misc)

   ============================================================= */

/* convert a float into an unsigned */
inline unsigned float2unsigned(float value)
{
	unsigned result;
	memcpy(&result, &value, sizeof value);
	return result;
}

/* convert an unsigned into a float */
inline float unsigned2float(unsigned value)
{
	float result;
	memcpy(&result, &value, sizeof value);
	return result;
}

/* convert integer into array of unsigned char - little indian */
inline void unsigned2char(unsigned value, unsigned char *buffer)
{
	buffer[0] = value & 0xFF;
	buffer[1] = (value >> 8) & 0xFF;
	buffer[2] = (value >> 16) & 0xFF;
	buffer[3] = (value >> 24) & 0xFF;
}

/* convert array of char into integer - little indian */
inline unsigned char2unsigned(unsigned char *buffer)
{
	return buffer[0] + (buffer[1] << 8) + (buffer[2] << 16) + (buffer[3] << 24);
}

/* the following six functions return the kind of the considered opcdoe */

bool is_branch(opcode_t opcode)
{
	return (opcode == BEQZ || opcode == BNEZ || opcode == BLTZ || opcode == BLEZ || opcode == BGTZ || opcode == BGEZ || opcode == JUMP);
}

bool is_memory(opcode_t opcode)
{
	return (opcode == LW || opcode == SW || opcode == LWS || opcode == SWS);
}

bool is_int_r(opcode_t opcode)
{
	return (opcode == ADD || opcode == SUB || opcode == XOR || opcode == AND);
}

bool is_int_imm(opcode_t opcode)
{
	return (opcode == ADDI || opcode == SUBI);
}

bool is_int(opcode_t opcode)
{
	return (is_int_r(opcode) || is_int_imm(opcode));
}

bool is_fp_alu(opcode_t opcode)
{
	return (opcode == ADDS || opcode == SUBS || opcode == MULTS || opcode == DIVS);
}

/* clears a ROB entry */
void clean_rob(rob_entry_t *entry)
{
	entry->ready = false;
	entry->pc = UNDEFINED;
	entry->state = ISSUE;
	entry->destination = UNDEFINED;
	entry->value = UNDEFINED;
	entry->store_bypassed = false;
}

/* clears a reservation station */
void clean_res_station(res_station_entry_t *entry)
{
	entry->pc = UNDEFINED;
	entry->value1 = UNDEFINED;
	entry->value2 = UNDEFINED;
	entry->tag1 = UNDEFINED;
	entry->tag2 = UNDEFINED;
	entry->destination = UNDEFINED;
	entry->address = UNDEFINED;
}

/* clears an entry if the instruction window */
void clean_instr_window(instr_window_entry_t *entry)
{
	entry->pc = UNDEFINED;
	entry->issue = UNDEFINED;
	entry->exe = UNDEFINED;
	entry->wr = UNDEFINED;
	entry->commit = UNDEFINED;
}

/* implements the ALU operation 
   NOTE: this function does not cover LOADS and STORES!
*/
unsigned alu(opcode_t opcode, unsigned value1, unsigned value2, unsigned immediate, unsigned pc)
{
	unsigned result;
	switch (opcode)
	{
	case ADD:
		result = value1 + value2;
		break;
	case ADDI:
		result = value1 + immediate;
		break;
	case SUB:
		result = value1 - value2;
		break;
	case SUBI:
		result = value1 - immediate;
		break;
	case XOR:
		result = value1 ^ value2;
		break;
	case AND:
		result = value1 & value2;
		break;
	case MULT:
		result = value1 * value2;
		break;
	case DIV:
		result = value1 / value2;
		break;
	case ADDS:
		result = float2unsigned(unsigned2float(value1) + unsigned2float(value2));
		break;
	case SUBS:
		result = float2unsigned(unsigned2float(value1) - unsigned2float(value2));
		break;
	case MULTS:
		result = float2unsigned(unsigned2float(value1) * unsigned2float(value2));
		break;
	case DIVS:
		result = float2unsigned(unsigned2float(value1) / unsigned2float(value2));
		break;
	case JUMP:
		result = pc + 4 + immediate;
		break;
	default: //branches
		int reg = (int)value1;
		bool condition = ((opcode == BEQZ && reg == 0) ||
						  (opcode == BNEZ && reg != 0) ||
						  (opcode == BGEZ && reg >= 0) ||
						  (opcode == BLEZ && reg <= 0) ||
						  (opcode == BGTZ && reg > 0) ||
						  (opcode == BLTZ && reg < 0));
		if (condition)
			result = pc + 4 + immediate;
		else
			result = pc + 4;
		break;
	}
	return result;
}

/* writes the data memory at the specified address */
void sim_ooo::write_memory(unsigned address, unsigned value)
{
	unsigned2char(value, data_memory + address);
}

/* =============================================================

   Handling of FUNCTIONAL UNITS

   ============================================================= */

/* initializes an execution unit */
void sim_ooo::init_exec_unit(exe_unit_t exec_unit, unsigned latency, unsigned instances)
{
	for (unsigned i = 0; i < instances; i++)
	{
		exec_units[num_units].type = exec_unit;
		exec_units[num_units].latency = latency;
		exec_units[num_units].busy = 0;
		exec_units[num_units].pc = UNDEFINED;
		num_units++;
	}
}

/* returns a free unit for that particular operation or UNDEFINED if no unit is currently available */
unsigned sim_ooo::get_free_unit(opcode_t opcode)
{
	if (num_units == 0)
	{
		cout << "ERROR:: simulator does not have any execution units!\n";
		exit(-1);
	}
	for (unsigned u = 0; u < num_units; u++)
	{
		switch (opcode)
		{
		//Integer unit
		case ADD:
		case ADDI:
		case SUB:
		case SUBI:
		case XOR:
		case AND:
		case BEQZ:
		case BNEZ:
		case BLTZ:
		case BGTZ:
		case BLEZ:
		case BGEZ:
		case JUMP:
			if (exec_units[u].type == INTEGER && exec_units[u].busy == 0 && exec_units[u].pc == UNDEFINED)
				return u;
			break;
		//memory unit
		case LW:
		case SW:
		case LWS:
		case SWS:
			if (exec_units[u].type == MEMORY && exec_units[u].busy == 0 && exec_units[u].pc == UNDEFINED)
				return u;
			break;
		// FP adder
		case ADDS:
		case SUBS:
			if (exec_units[u].type == ADDER && exec_units[u].busy == 0 && exec_units[u].pc == UNDEFINED)
				return u;
			break;
		// Multiplier
		case MULT:
		case MULTS:
			if (exec_units[u].type == MULTIPLIER && exec_units[u].busy == 0 && exec_units[u].pc == UNDEFINED)
				return u;
			break;
		// Divider
		case DIV:
		case DIVS:
			if (exec_units[u].type == DIVIDER && exec_units[u].busy == 0 && exec_units[u].pc == UNDEFINED)
				return u;
			break;
		default:
			cout << "ERROR:: operations not requiring exec unit!\n";
			exit(-1);
		}
	}
	return UNDEFINED;
}

/* ============================================================================

   Primitives used to print out the state of each component of the processor:
   	- registers
	- data memory
	- instruction window
        - reservation stations and load buffers
        - (cycle-by-cycle) execution log
	- execution statistics (CPI, # instructions executed, # clock cycles) 

   =========================================================================== */

/* prints the content of the data memory */
void sim_ooo::print_memory(unsigned start_address, unsigned end_address)
{
	cout << "DATA MEMORY[0x" << hex << setw(8) << setfill('0') << start_address << ":0x" << hex << setw(8) << setfill('0') << end_address << "]" << endl;
	for (unsigned i = start_address; i < end_address; i++)
	{
		if (i % 4 == 0)
			cout << "0x" << hex << setw(8) << setfill('0') << i << ": ";
		cout << hex << setw(2) << setfill('0') << int(data_memory[i]) << " ";
		if (i % 4 == 3)
		{
			cout << endl;
		}
	}
}

/* prints the value of the registers */
void sim_ooo::print_registers()
{
	unsigned i;
	cout << "GENERAL PURPOSE REGISTERS" << endl;
	cout << setfill(' ') << setw(8) << "Register" << setw(22) << "Value" << setw(5) << "ROB" << endl;
	for (i = 0; i < NUM_GP_REGISTERS; i++)
	{
		if (get_int_register_tag(i) != UNDEFINED)
			cout << setfill(' ') << setw(7) << "R" << dec << i << setw(22) << "-" << setw(5) << get_int_register_tag(i) << endl;
		else if (get_int_register(i) != (int)UNDEFINED)
			cout << setfill(' ') << setw(7) << "R" << dec << i << setw(11) << get_int_register(i) << hex << "/0x" << setw(8) << setfill('0') << get_int_register(i) << setfill(' ') << setw(5) << "-" << endl;
	}
	for (i = 0; i < NUM_GP_REGISTERS; i++)
	{
		if (get_fp_register_tag(i) != UNDEFINED)
			cout << setfill(' ') << setw(7) << "F" << dec << i << setw(22) << "-" << setw(5) << get_fp_register_tag(i) << endl;
		else if (get_fp_register(i) != UNDEFINED)
			cout << setfill(' ') << setw(7) << "F" << dec << i << setw(11) << get_fp_register(i) << hex << "/0x" << setw(8) << setfill('0') << float2unsigned(get_fp_register(i)) << setfill(' ') << setw(5) << "-" << endl;
	}
	cout << endl;
}

/* prints the content of the ROB */
void sim_ooo::print_rob()
{
	cout << "REORDER BUFFER" << endl;
	cout << setfill(' ') << setw(5) << "Entry" << setw(6) << "Busy" << setw(7) << "Ready" << setw(12) << "PC" << setw(10) << "State" << setw(6) << "Dest" << setw(12) << "Value" << endl;
	for (unsigned i = 0; i < rob.num_entries; i++)
	{
		rob_entry_t entry = rob.entries[i];
		instruction_t instruction;
		if (entry.pc != UNDEFINED)
			instruction = instr_memory[(entry.pc - instr_base_address) >> 2];
		cout << setfill(' ');
		cout << setw(5) << i;
		cout << setw(6);
		if (entry.pc == UNDEFINED)
			cout << "no";
		else
			cout << "yes";
		cout << setw(7);
		if (entry.ready)
			cout << "yes";
		else
			cout << "no";
		if (entry.pc != UNDEFINED)
			cout << "  0x" << hex << setfill('0') << setw(8) << entry.pc;
		else
			cout << setw(12) << "-";
		cout << setfill(' ') << setw(10);
		if (entry.pc == UNDEFINED)
			cout << "-";
		else
			cout << stage_names[entry.state];
		if (entry.destination == UNDEFINED)
			cout << setw(6) << "-";
		else
		{
			if (instruction.opcode == SW || instruction.opcode == SWS)
				cout << setw(6) << dec << entry.destination;
			else if (entry.destination < NUM_GP_REGISTERS)
				cout << setw(5) << "R" << dec << entry.destination;
			else
				cout << setw(5) << "F" << dec << entry.destination - NUM_GP_REGISTERS;
		}
		if (entry.value != UNDEFINED)
			cout << "  0x" << hex << setw(8) << setfill('0') << entry.value << endl;
		else
			cout << setw(12) << setfill(' ') << "-" << endl;
	}
	cout << endl;
}

/* prints the content of the reservation stations */
void sim_ooo::print_reservation_stations()
{
	cout << "RESERVATION STATIONS" << endl;
	cout << setfill(' ');
	cout << setw(7) << "Name" << setw(6) << "Busy" << setw(12) << "PC" << setw(12) << "Vj" << setw(12) << "Vk" << setw(6) << "Qj" << setw(6) << "Qk" << setw(6) << "Dest" << setw(12) << "Address" << endl;
	for (unsigned i = 0; i < reservation_stations.num_entries; i++)
	{
		res_station_entry_t entry = reservation_stations.entries[i];
		cout << setfill(' ');
		cout << setw(6);
		cout << res_station_names[entry.type];
		cout << entry.name + 1;
		cout << setw(6);
		if (entry.pc == UNDEFINED)
			cout << "no";
		else
			cout << "yes";
		if (entry.pc != UNDEFINED)
			cout << setw(4) << "  0x" << hex << setfill('0') << setw(8) << entry.pc;
		else
			cout << setfill(' ') << setw(12) << "-";
		if (entry.value1 != UNDEFINED)
			cout << "  0x" << setfill('0') << setw(8) << hex << entry.value1;
		else
			cout << setfill(' ') << setw(12) << "-";
		if (entry.value2 != UNDEFINED)
			cout << "  0x" << setfill('0') << setw(8) << hex << entry.value2;
		else
			cout << setfill(' ') << setw(12) << "-";
		cout << setfill(' ');
		cout << setw(6);
		if (entry.tag1 != UNDEFINED)
			cout << dec << entry.tag1;
		else
			cout << "-";
		cout << setw(6);
		if (entry.tag2 != UNDEFINED)
			cout << dec << entry.tag2;
		else
			cout << "-";
		cout << setw(6);
		if (entry.destination != UNDEFINED)
			cout << dec << entry.destination;
		else
			cout << "-";
		if (entry.address != UNDEFINED)
			cout << setw(4) << "  0x" << setfill('0') << setw(8) << hex << entry.address;
		else
			cout << setfill(' ') << setw(12) << "-";
		cout << endl;
	}
	cout << endl;
}

/* prints the state of the pending instructions */
void sim_ooo::print_pending_instructions()
{
	cout << "PENDING INSTRUCTIONS STATUS" << endl;
	cout << setfill(' ');
	cout << setw(10) << "PC" << setw(7) << "Issue" << setw(7) << "Exe" << setw(7) << "WR" << setw(7) << "Commit";
	cout << endl;
	for (unsigned i = 0; i < pending_instructions.num_entries; i++)
	{
		instr_window_entry_t entry = pending_instructions.entries[i];
		if (entry.pc != UNDEFINED)
			cout << "0x" << setfill('0') << setw(8) << hex << entry.pc;
		else
			cout << setfill(' ') << setw(10) << "-";
		cout << setfill(' ');
		cout << setw(7);
		if (entry.issue != UNDEFINED)
			cout << dec << entry.issue;
		else
			cout << "-";
		cout << setw(7);
		if (entry.exe != UNDEFINED)
			cout << dec << entry.exe;
		else
			cout << "-";
		cout << setw(7);
		if (entry.wr != UNDEFINED)
			cout << dec << entry.wr;
		else
			cout << "-";
		cout << setw(7);
		if (entry.commit != UNDEFINED)
			cout << dec << entry.commit;
		else
			cout << "-";
		cout << endl;
	}
	cout << endl;
}

/* initializes the execution log */
void sim_ooo::init_log()
{
	log << "EXECUTION LOG" << endl;
	log << setfill(' ');
	log << setw(10) << "PC" << setw(7) << "Issue" << setw(7) << "Exe" << setw(7) << "WR" << setw(7) << "Commit";
	log << endl;
}

/* adds an instruction to the log */
void sim_ooo::commit_to_log(instr_window_entry_t entry)
{
	if (entry.pc != UNDEFINED)
		log << "0x" << setfill('0') << setw(8) << hex << entry.pc;
	else
		log << setfill(' ') << setw(10) << "-";
	log << setfill(' ');
	log << setw(7);
	if (entry.issue != UNDEFINED)
		log << dec << entry.issue;
	else
		log << "-";
	log << setw(7);
	if (entry.exe != UNDEFINED)
		log << dec << entry.exe;
	else
		log << "-";
	log << setw(7);
	if (entry.wr != UNDEFINED)
		log << dec << entry.wr;
	else
		log << "-";
	log << setw(7);
	if (entry.commit != UNDEFINED)
		log << dec << entry.commit;
	else
		log << "-";
	log << endl;
}

/* prints the content of the log */
void sim_ooo::print_log()
{
	cout << log.str();
}

/* prints the state of the pending instruction, the content of the ROB, the content of the reservation stations and of the registers */
void sim_ooo::print_status()
{
	print_pending_instructions();
	print_rob();
	print_reservation_stations();
	print_registers();
}

/* execution statistics */

float sim_ooo::get_IPC() { return (float)instructions_executed / clock_cycles; }

unsigned sim_ooo::get_instructions_executed() { return instructions_executed; }

unsigned sim_ooo::get_clock_cycles() { return clock_cycles; }

/* ============================================================================

   PARSER

   =========================================================================== */

void sim_ooo::load_program(const char *filename, unsigned base_address)
{

	/* initializing the base instruction address */
	instr_base_address = base_address;
	PC = base_address;

	/* creating a map with the valid opcodes and with the valid labels */
	map<string, opcode_t> opcodes; //for opcodes
	map<string, unsigned> labels;  //for branches
	for (int i = 0; i < NUM_OPCODES; i++)
		opcodes[string(instr_names[i])] = (opcode_t)i;

	/* opening the assembly file */
	ifstream fin(filename, ios::in | ios::binary);
	if (!fin.is_open())
	{
		cerr << "error: open file " << filename << " failed!" << endl;
		exit(-1);
	}

	/* parsing the assembly file line by line */
	string line;
	unsigned instruction_nr = 0;
	while (getline(fin, line))
	{

		// set the instruction field
		char *str = const_cast<char *>(line.c_str());

		// tokenize the instruction
		char *token = strtok(str, " \t");
		map<string, opcode_t>::iterator search = opcodes.find(token);
		if (search == opcodes.end())
		{
			// this is a label for a branch - extract it and save it in the labels map
			string label = string(token).substr(0, string(token).length() - 1);
			labels[label] = instruction_nr;
			// move to next token, which must be the instruction opcode
			token = strtok(NULL, " \t");
			search = opcodes.find(token);
			if (search == opcodes.end())
				cout << "ERROR: invalid opcode: " << token << " !" << endl;
		}

		instr_memory[instruction_nr].opcode = search->second;

		//reading remaining parameters
		char *par1;
		char *par2;
		char *par3;
		switch (instr_memory[instruction_nr].opcode)
		{
		case ADD:
		case SUB:
		case XOR:
		case AND:
		case MULT:
		case DIV:
		case ADDS:
		case SUBS:
		case MULTS:
		case DIVS:
			par1 = strtok(NULL, " \t");
			par2 = strtok(NULL, " \t");
			par3 = strtok(NULL, " \t");
			instr_memory[instruction_nr].dest = atoi(strtok(par1, "RF"));
			instr_memory[instruction_nr].src1 = atoi(strtok(par2, "RF"));
			instr_memory[instruction_nr].src2 = atoi(strtok(par3, "RF"));
			break;
		case ADDI:
		case SUBI:
			par1 = strtok(NULL, " \t");
			par2 = strtok(NULL, " \t");
			par3 = strtok(NULL, " \t");
			instr_memory[instruction_nr].dest = atoi(strtok(par1, "R"));
			instr_memory[instruction_nr].src1 = atoi(strtok(par2, "R"));
			instr_memory[instruction_nr].immediate = strtoul(par3, NULL, 0);
			break;
		case LW:
		case LWS:
			par1 = strtok(NULL, " \t");
			par2 = strtok(NULL, " \t");
			instr_memory[instruction_nr].dest = atoi(strtok(par1, "RF"));
			instr_memory[instruction_nr].immediate = strtoul(strtok(par2, "()"), NULL, 0);
			instr_memory[instruction_nr].src1 = atoi(strtok(NULL, "R"));
			break;
		case SW:
		case SWS:
			par1 = strtok(NULL, " \t");
			par2 = strtok(NULL, " \t");
			instr_memory[instruction_nr].src1 = atoi(strtok(par1, "RF"));
			instr_memory[instruction_nr].immediate = strtoul(strtok(par2, "()"), NULL, 0);
			instr_memory[instruction_nr].src2 = atoi(strtok(NULL, "R"));
			break;
		case BEQZ:
		case BNEZ:
		case BLTZ:
		case BGTZ:
		case BLEZ:
		case BGEZ:
			par1 = strtok(NULL, " \t");
			par2 = strtok(NULL, " \t");
			instr_memory[instruction_nr].src1 = atoi(strtok(par1, "R"));
			instr_memory[instruction_nr].label = par2;
			break;
		case JUMP:
			par2 = strtok(NULL, " \t");
			instr_memory[instruction_nr].label = par2;
		default:
			break;
		}

		/* increment instruction number before moving to next line */
		instruction_nr++;
	}
	//reconstructing the labels of the branch operations
	int i = 0;
	while (true)
	{
		instruction_t instr = instr_memory[i];
		if (instr.opcode == EOP)
			break;
		if (instr.opcode == BLTZ || instr.opcode == BNEZ ||
			instr.opcode == BGTZ || instr.opcode == BEQZ ||
			instr.opcode == BGEZ || instr.opcode == BLEZ ||
			instr.opcode == JUMP)
		{
			instr_memory[i].immediate = (labels[instr.label] - i - 1) << 2;
		}
		i++;
	}
}

/* ============================================================================

   Simulator creation, initialization and deallocation 

   =========================================================================== */

sim_ooo::sim_ooo(unsigned mem_size,
				 unsigned rob_size,
				 unsigned num_int_res_stations,
				 unsigned num_add_res_stations,
				 unsigned num_mul_res_stations,
				 unsigned num_load_res_stations,
				 unsigned max_issue)
{
	//memory
	data_memory_size = mem_size;
	data_memory = new unsigned char[data_memory_size];

	//issue width
	issue_width = max_issue;

	//rob, instruction window, reservation stations
	rob.num_entries = rob_size;
	pending_instructions.num_entries = rob_size;
	reservation_stations.num_entries = num_int_res_stations + num_load_res_stations + num_add_res_stations + num_mul_res_stations;
	rob.entries = new rob_entry_t[rob_size];
	pending_instructions.entries = new instr_window_entry_t[rob_size];
	reservation_stations.entries = new res_station_entry_t[reservation_stations.num_entries];
	unsigned n = 0;
	for (unsigned i = 0; i < num_int_res_stations; i++, n++)
	{
		reservation_stations.entries[n].type = INTEGER_RS;
		reservation_stations.entries[n].name = i;
	}
	for (unsigned i = 0; i < num_load_res_stations; i++, n++)
	{
		reservation_stations.entries[n].type = LOAD_B;
		reservation_stations.entries[n].name = i;
	}
	for (unsigned i = 0; i < num_add_res_stations; i++, n++)
	{
		reservation_stations.entries[n].type = ADD_RS;
		reservation_stations.entries[n].name = i;
	}
	for (unsigned i = 0; i < num_mul_res_stations; i++, n++)
	{
		reservation_stations.entries[n].type = MULT_RS;
		reservation_stations.entries[n].name = i;
	}
	//execution units
	num_units = 0;
	reset();
}

sim_ooo::~sim_ooo()
{
	delete[] data_memory;
	delete[] rob.entries;
	delete[] pending_instructions.entries;
	delete[] reservation_stations.entries;
}

/* =============================================================

   CODE TO BE COMPLETED

   ============================================================= */

/* core of the simulator */
void sim_ooo::run(unsigned cycles)
{
	issue_struct_stall = false; // resetting the struct hazard flag
	int issue_counter = issue_width;
	bool willBranch = false;
	int loadReleasedUnit = 99;
	cout << "\nPC is:" << PC << "\n";

ISSUE_STAGE:
	//detecting if the reservation station is full or not
	vacantPlace = false; //if it turns true then there's a vacant place in the Reservation station
						 //Checking the reservation stations without adding anything to them first
	if (is_memory(instr_memory[(PC - instr_base_address) / 0x00000004].opcode))
	{
		for (int i = 0; i < reservation_stations.num_entries; i++)
		{
			if (reservation_stations.entries[i].type == LOAD_B && reservation_stations.entries[i].pc == UNDEFINED)
			{
				vacantPlace = true;
				break;
			}
		}
		if (vacantPlace == false)
		{
			issue_struct_stall = true;
		}
	}

	if (is_int(instr_memory[(PC - instr_base_address) / 0x00000004].opcode))
	{
		for (int i = 0; i < reservation_stations.num_entries; i++)
		{
			if (reservation_stations.entries[i].type == INTEGER_RS && reservation_stations.entries[i].pc == UNDEFINED)
			{
				vacantPlace = true;
				break;
			}
		}
		if (vacantPlace == false)
		{
			issue_struct_stall = true;
		}
	}

	if (is_branch(instr_memory[(PC - instr_base_address) / 0x00000004].opcode))
	{
		for (int i = 0; i < reservation_stations.num_entries; i++)
		{
			if (reservation_stations.entries[i].type == INTEGER_RS && reservation_stations.entries[i].pc == UNDEFINED)
			{
				vacantPlace = true;
				break;
			}
		}
		if (vacantPlace == false)
		{
			issue_struct_stall = true;
		}
	}

	if (instr_memory[(PC - instr_base_address) / 0x00000004].opcode == ADDS || instr_memory[(PC - instr_base_address) / 0x00000004].opcode == SUBS)
	{
		for (int i = 0; i < reservation_stations.num_entries; i++)
		{
			if (reservation_stations.entries[i].type == ADD_RS && reservation_stations.entries[i].pc == UNDEFINED)
			{
				vacantPlace = true;
				break;
			}
		}
		if (vacantPlace == false)
		{
			issue_struct_stall = true;
		}
	}

	if (instr_memory[(PC - instr_base_address) / 0x00000004].opcode == MULTS || instr_memory[(PC - instr_base_address) / 0x00000004].opcode == DIVS)
	{
		for (int i = 0; i < reservation_stations.num_entries; i++)
		{
			if (reservation_stations.entries[i].type == MULT_RS && reservation_stations.entries[i].pc == UNDEFINED)
			{
				vacantPlace = true;
				break;
			}
		}
		if (vacantPlace == false)
		{
			issue_struct_stall = true;
		}
	}

	//Issue stage
	if (instr_memory[(PC - instr_base_address) / 0x00000004].opcode != EOP && issue_struct_stall == false)
	{
		if (ROBentryIndex == rob.num_entries)
		{
			ROBentryIndex = 0;
		}
		if (rob.entries[ROBentryIndex].pc == UNDEFINED)
		{
			rob.entries[ROBentryIndex].pc = PC;
			if (is_fp_alu(instr_memory[(PC - instr_base_address) / 0x00000004].opcode) || instr_memory[(PC - instr_base_address) / 0x00000004].opcode == LWS)
			{
				rob.entries[ROBentryIndex].destination = instr_memory[(PC - instr_base_address) / 0x00000004].dest + NUM_GP_REGISTERS;
			}
			else
			{
				rob.entries[ROBentryIndex].destination = instr_memory[(PC - instr_base_address) / 0x00000004].dest;
			}
			rob.entries[ROBentryIndex].state = ISSUE;
			rob.entries[ROBentryIndex].value = UNDEFINED;
			ROBindex4ResStations = ROBentryIndex;
			pending_instructions.entries[ROBentryIndex].pc = PC;
			pending_instructions.entries[ROBentryIndex].issue = clock_cycles;
			ROBentryIndex++;
		}
		else if (rob.entries[ROBentryIndex].pc != UNDEFINED)
		{
			issue_struct_stall = true; //full ROB detected, a stall is needed
		}

		if (issue_struct_stall == false)
		{
			if (instr_memory[(PC - instr_base_address) / 0x00000004].opcode == LW || instr_memory[(PC - instr_base_address) / 0x00000004].opcode == LWS)
			{
				for (int i = 0; i < reservation_stations.num_entries; i++)
				{
					if (reservation_stations.entries[i].type == LOAD_B && reservation_stations.entries[i].pc == UNDEFINED)
					{
						reservation_stations.entries[i].pc = PC;
						reservation_stations.entries[i].address = instr_memory[(PC - instr_base_address) / 0x00000004].immediate;
						reservation_stations.entries[i].destination = ROBindex4ResStations;
						if (INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1] == UNDEFINED)
						{
							reservation_stations.entries[i].value1 = INT_regs[instr_memory[(PC - instr_base_address) / 0x00000004].src1];
						}
						else if (INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1] != UNDEFINED && rob.entries[INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1]].value != UNDEFINED)
						{
							reservation_stations.entries[i].value1 = rob.entries[INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1]].value;
						}
						else if (INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1] != UNDEFINED && rob.entries[INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1]].value == UNDEFINED)
						{
							reservation_stations.entries[i].tag1 = INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1];
						}
						if (instr_memory[(PC - instr_base_address) / 0x00000004].opcode == LWS)
						{
							FP_tags[instr_memory[(PC - instr_base_address) / 0x00000004].dest] = ROBindex4ResStations;
						}
						else if (instr_memory[(PC - instr_base_address) / 0x00000004].opcode == LW)
						{
							INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].dest] = ROBindex4ResStations;
						}
						break;
					}
				}
			}

			//STORE DONE HERE
			if (instr_memory[(PC - instr_base_address) / 0x00000004].opcode == SWS)
			{
				for (int i = 0; i < reservation_stations.num_entries; i++)
				{
					if (reservation_stations.entries[i].type == LOAD_B && reservation_stations.entries[i].pc == UNDEFINED)
					{
						reservation_stations.entries[i].pc = PC;
						reservation_stations.entries[i].address = instr_memory[(PC - instr_base_address) / 0x00000004].immediate;
						reservation_stations.entries[i].destination = ROBindex4ResStations;
						//source 1 is FP (value to be inserted in memory)
						if (FP_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1] == UNDEFINED)
						{
							reservation_stations.entries[i].value1 = float2unsigned(FP_regs[instr_memory[(PC - instr_base_address) / 0x00000004].src1]);
						}
						else if (FP_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1] != UNDEFINED && rob.entries[FP_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1]].value != UNDEFINED)
						{
							reservation_stations.entries[i].value1 = rob.entries[FP_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1]].value;
						}
						else if (FP_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1] != UNDEFINED && rob.entries[FP_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1]].value == UNDEFINED)
						{
							reservation_stations.entries[i].tag1 = FP_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1];
						}
						//source 2
						if (INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src2] == UNDEFINED)
						{
							reservation_stations.entries[i].value2 = INT_regs[instr_memory[(PC - instr_base_address) / 0x00000004].src2];
						}
						else if (INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src2] != UNDEFINED && rob.entries[INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src2]].value != UNDEFINED)
						{
							reservation_stations.entries[i].value2 = rob.entries[INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src2]].value;
						}
						else if (INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src2] != UNDEFINED && rob.entries[INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src2]].value == UNDEFINED)
						{
							reservation_stations.entries[i].tag2 = INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src2];
						}
						break;
					}
				}
			}

			if (is_int_r(instr_memory[(PC - instr_base_address) / 0x00000004].opcode))
			{
				for (int i = 0; i < reservation_stations.num_entries; i++)
				{
					if (reservation_stations.entries[i].type == INTEGER_RS && reservation_stations.entries[i].pc == UNDEFINED)
					{
						reservation_stations.entries[i].pc = PC;
						reservation_stations.entries[i].destination = ROBindex4ResStations;
						if (INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1] == UNDEFINED)
						{
							reservation_stations.entries[i].value1 = INT_regs[instr_memory[(PC - instr_base_address) / 0x00000004].src1];
						}
						else if (INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1] != UNDEFINED && rob.entries[INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1]].value != UNDEFINED)
						{
							reservation_stations.entries[i].value1 = rob.entries[INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1]].value;
						}
						else if (INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1] != UNDEFINED && rob.entries[INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1]].value == UNDEFINED)
						{
							reservation_stations.entries[i].tag1 = INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1];
						}
						//value 2
						if (INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src2] == UNDEFINED)
						{
							reservation_stations.entries[i].value2 = INT_regs[instr_memory[(PC - instr_base_address) / 0x00000004].src2];
						}
						else if (INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src2] != UNDEFINED && rob.entries[INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src2]].value != UNDEFINED)
						{
							reservation_stations.entries[i].value1 = rob.entries[INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src2]].value;
						}
						else if (INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src2] != UNDEFINED && rob.entries[INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src2]].value == UNDEFINED)
						{
							reservation_stations.entries[i].tag2 = INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src2];
						}
						if ((instr_memory[(PC - instr_base_address) / 0x00000004].src2 == instr_memory[(PC - instr_base_address) / 0x00000004].src1) && reservation_stations.entries[i].value1 != UNDEFINED)
						{
							reservation_stations.entries[i].value2 = reservation_stations.entries[i].value1;
						}
						INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].dest] = ROBindex4ResStations;
						break;
					}
				}
			}

			if (is_int_imm(instr_memory[(PC - instr_base_address) / 0x00000004].opcode))
			{
				for (int i = 0; i < reservation_stations.num_entries; i++)
				{
					if (reservation_stations.entries[i].type == INTEGER_RS && reservation_stations.entries[i].pc == UNDEFINED)
					{
						reservation_stations.entries[i].pc = PC;
						reservation_stations.entries[i].destination = ROBindex4ResStations;
						if (INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1] == UNDEFINED)
						{
							reservation_stations.entries[i].value1 = INT_regs[instr_memory[(PC - instr_base_address) / 0x00000004].src1];
						}
						else if (INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1] != UNDEFINED && rob.entries[INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1]].value != UNDEFINED)
						{
							reservation_stations.entries[i].value1 = rob.entries[INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1]].value;
						}
						else if (INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1] != UNDEFINED && rob.entries[INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1]].value == UNDEFINED)
						{
							reservation_stations.entries[i].tag1 = INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1];
						}
						INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].dest] = ROBindex4ResStations;
						break;
					}
				}
			}

			if (is_branch(instr_memory[(PC - instr_base_address) / 0x00000004].opcode))
			{
				for (int i = 0; i < reservation_stations.num_entries; i++)
				{
					if (reservation_stations.entries[i].type == INTEGER_RS && reservation_stations.entries[i].pc == UNDEFINED)
					{
						reservation_stations.entries[i].pc = PC;
						if (INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1] == UNDEFINED)
						{
							reservation_stations.entries[i].value1 = INT_regs[instr_memory[(PC - instr_base_address) / 0x00000004].src1];
						}
						else if (INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1] != UNDEFINED && rob.entries[INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1]].value != UNDEFINED)
						{
							reservation_stations.entries[i].value1 = rob.entries[INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1]].value;
						}
						else if (INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1] != UNDEFINED && rob.entries[INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1]].value == UNDEFINED)
						{
							reservation_stations.entries[i].tag1 = INT_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1];
						}
						reservation_stations.entries[i].destination = ROBindex4ResStations;
						break;
					}
				}
			}

			if (instr_memory[(PC - instr_base_address) / 0x00000004].opcode == ADDS || instr_memory[(PC - instr_base_address) / 0x00000004].opcode == SUBS)
			{
				for (int i = 0; i < reservation_stations.num_entries; i++)
				{
					if (reservation_stations.entries[i].type == ADD_RS && reservation_stations.entries[i].pc == UNDEFINED)
					{
						reservation_stations.entries[i].pc = PC;
						reservation_stations.entries[i].destination = ROBindex4ResStations;
						if (FP_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1] == UNDEFINED)
						{
							reservation_stations.entries[i].value1 = float2unsigned(FP_regs[instr_memory[(PC - instr_base_address) / 0x00000004].src1]);
						}
						else if (FP_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1] != UNDEFINED && rob.entries[FP_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1]].value != UNDEFINED)
						{
							reservation_stations.entries[i].value1 = rob.entries[FP_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1]].value;
						}
						else if (FP_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1] != UNDEFINED && rob.entries[FP_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1]].value == UNDEFINED)
						{
							reservation_stations.entries[i].tag1 = FP_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1];
						}
						//value 2
						if (FP_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src2] == UNDEFINED)
						{
							reservation_stations.entries[i].value2 = float2unsigned(FP_regs[instr_memory[(PC - instr_base_address) / 0x00000004].src2]);
						}
						else if (FP_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src2] != UNDEFINED && rob.entries[FP_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src2]].value != UNDEFINED)
						{
							reservation_stations.entries[i].value2 = rob.entries[FP_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src2]].value;
						}
						else if (FP_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src2] != UNDEFINED && rob.entries[FP_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src2]].value == UNDEFINED)
						{
							reservation_stations.entries[i].tag2 = FP_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src2];
						}
						FP_tags[instr_memory[(PC - instr_base_address) / 0x00000004].dest] = ROBindex4ResStations;
						break;
					}
				}
			}

			if (instr_memory[(PC - instr_base_address) / 0x00000004].opcode == MULTS || instr_memory[(PC - instr_base_address) / 0x00000004].opcode == DIVS)
			{
				for (int i = 0; i < reservation_stations.num_entries; i++)
				{
					if (reservation_stations.entries[i].type == MULT_RS && reservation_stations.entries[i].pc == UNDEFINED)
					{
						reservation_stations.entries[i].pc = PC;
						reservation_stations.entries[i].destination = ROBindex4ResStations;
						if (FP_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1] == UNDEFINED)
						{
							reservation_stations.entries[i].value1 = float2unsigned(FP_regs[instr_memory[(PC - instr_base_address) / 0x00000004].src1]);
						}
						else if (FP_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1] != UNDEFINED && rob.entries[FP_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1]].value != UNDEFINED)
						{
							reservation_stations.entries[i].value1 = rob.entries[FP_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1]].value;
						}
						else if (FP_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1] != UNDEFINED && rob.entries[FP_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1]].value == UNDEFINED)
						{
							reservation_stations.entries[i].tag1 = FP_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src1];
						}
						//value 2
						if (FP_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src2] == UNDEFINED)
						{
							reservation_stations.entries[i].value2 = float2unsigned(FP_regs[instr_memory[(PC - instr_base_address) / 0x00000004].src2]);
						}
						else if (FP_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src2] != UNDEFINED && rob.entries[FP_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src2]].value != UNDEFINED)
						{
							reservation_stations.entries[i].value2 = rob.entries[FP_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src2]].value;
						}
						else if (FP_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src2] != UNDEFINED && rob.entries[FP_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src2]].value == UNDEFINED)
						{
							reservation_stations.entries[i].tag2 = FP_tags[instr_memory[(PC - instr_base_address) / 0x00000004].src2];
						}
						FP_tags[instr_memory[(PC - instr_base_address) / 0x00000004].dest] = ROBindex4ResStations;
						break;
					}
				}
			}
		}
	}
	issue_counter--;
	if (issue_counter > 0 && issue_struct_stall == false && instr_memory[(PC - instr_base_address + 0x00000004) / 0x00000004].opcode != EOP)
	{
		PC += 0x00000004;
		goto ISSUE_STAGE;
	}

	//Execution Stage
	cout << "Entering EX";
	//EX stage for STORE section
	for (int i = 0; i < reservation_stations.num_entries; i++)
	{ //checking for available execution units
		if (reservation_stations.entries[i].destination != UNDEFINED)
		{
			if (pending_instructions.entries[reservation_stations.entries[i].destination].issue < clock_cycles && rob.entries[reservation_stations.entries[i].destination].state == ISSUE && reservation_stations.entries[i].tag1 == UNDEFINED && reservation_stations.entries[i].tag2 == UNDEFINED && instr_memory[(reservation_stations.entries[i].pc - instr_base_address) / 0x00000004].opcode == SWS)
			{
				if (pending_instructions.entries[reservation_stations.entries[i].destination].issue < clock_cycles)
				{
					rob.entries[reservation_stations.entries[i].destination].destination = instr_memory[(reservation_stations.entries[i].pc - instr_base_address) / 0x00000004].immediate + reservation_stations.entries[i].value2;
					reservation_stations.entries[i].address = rob.entries[reservation_stations.entries[i].destination].destination;
					rob.entries[reservation_stations.entries[i].destination].state = EXECUTE;
					pending_instructions.entries[reservation_stations.entries[i].destination].exe = clock_cycles;
				}
			}
		}
	}

	//End of STORE execution and beginning of Other Execution stage
	for (int i = 0; i < reservation_stations.num_entries; i++)
	{ //checking for available execution units
		if (reservation_stations.entries[i].pc < PC && rob.entries[reservation_stations.entries[i].destination].state == ISSUE && get_free_unit(instr_memory[(reservation_stations.entries[i].pc - instr_base_address) / 0x00000004].opcode) != UNDEFINED && reservation_stations.entries[i].tag1 == UNDEFINED && reservation_stations.entries[i].tag2 == UNDEFINED && instr_memory[(reservation_stations.entries[i].pc - instr_base_address) / 0x00000004].opcode != SWS)
		{
			if (pending_instructions.entries[reservation_stations.entries[i].destination].issue < clock_cycles)
			{
				int theExecUnitNum = get_free_unit(instr_memory[(reservation_stations.entries[i].pc - instr_base_address) / 0x00000004].opcode); //saving the free execution unit's index number
				exec_units[theExecUnitNum].ALUoutput = alu(instr_memory[(reservation_stations.entries[i].pc - instr_base_address) / 0x00000004].opcode, reservation_stations.entries[i].value1, reservation_stations.entries[i].value2, instr_memory[(reservation_stations.entries[i].pc - instr_base_address) / 0x00000004].immediate, reservation_stations.entries[i].pc);
				if (instr_memory[(reservation_stations.entries[i].pc - instr_base_address) / 0x00000004].opcode == LWS || instr_memory[(reservation_stations.entries[i].pc - instr_base_address) / 0x00000004].opcode == LW)
				{
					for (int j = 0; j < reservation_stations.num_entries; j++)
					{
						if (reservation_stations.entries[j].pc != UNDEFINED)
						{
							if (instr_memory[(reservation_stations.entries[j].pc - instr_base_address) / 0x00000004].opcode == SWS && reservation_stations.entries[j].pc < reservation_stations.entries[i].pc)
							{
								if ((reservation_stations.entries[j].tag2 == UNDEFINED && rob.entries[reservation_stations.entries[j].destination].state == ISSUE && reservation_stations.entries[j].value2 + reservation_stations.entries[j].address == reservation_stations.entries[i].value1 + reservation_stations.entries[i].address) || (rob.entries[reservation_stations.entries[j].destination].state != ISSUE && reservation_stations.entries[j].address == reservation_stations.entries[i].value1 + reservation_stations.entries[i].address))
								{
									goto RAW_MEM_STALL;
								}
								if (reservation_stations.entries[j].tag2 != UNDEFINED)
								{
									goto RAW_MEM_STALL;
								}
							}
						}
					}

					for (int j = 0; j < rob.num_entries; j++)
					{
						if (rob.entries[j].pc != UNDEFINED)
						{
							if (instr_memory[(rob.entries[j].pc - instr_base_address) / 0x00000004].opcode == SWS && rob.entries[j].pc < reservation_stations.entries[i].pc)
							{
								if (rob.entries[j].destination == reservation_stations.entries[i].value1 + reservation_stations.entries[i].address && (rob.entries[j].state == WRITE_RESULT || rob.entries[j].state == COMMIT))
								{
									goto RAW_MEM_STALL;
								}
							}
						}
					}

					unsigned char *dataptr = &data_memory[reservation_stations.entries[i].value1 + reservation_stations.entries[i].address];
					reservation_stations.entries[i].address = reservation_stations.entries[i].value1 + reservation_stations.entries[i].address;
					exec_units[theExecUnitNum].ALUoutput = char2unsigned(dataptr);
				}
				exec_units[theExecUnitNum].pc = reservation_stations.entries[i].pc;
				rob.entries[reservation_stations.entries[i].destination].state = EXECUTE;
				pending_instructions.entries[reservation_stations.entries[i].destination].exe = clock_cycles;
				cout << "Past pc assignment";
				exec_units[theExecUnitNum].busy = exec_units[theExecUnitNum].latency;
			}
		RAW_MEM_STALL:;
		}
	}

	//Load Bypass section

	for (int i = 0; i < reservation_stations.num_entries; i++)
	{
		if (reservation_stations.entries[i].pc != UNDEFINED)
		{
			if ((instr_memory[(reservation_stations.entries[i].pc - instr_base_address) / 0x00000004].opcode == LWS || instr_memory[(reservation_stations.entries[i].pc - instr_base_address) / 0x00000004].opcode == LW) && rob.entries[reservation_stations.entries[i].destination].state == ISSUE && reservation_stations.entries[i].tag1 == UNDEFINED && pending_instructions.entries[reservation_stations.entries[i].destination].issue < clock_cycles)
			{
				for (int j = 0; j < rob.num_entries; j++)
				{
					if (rob.entries[j].pc != UNDEFINED)
					{
						if (instr_memory[(rob.entries[j].pc - instr_base_address) / 0x00000004].opcode == SWS && (rob.entries[j].state == WRITE_RESULT || rob.entries[j].state == COMMIT) && rob.entries[j].destination == reservation_stations.entries[i].value1 + reservation_stations.entries[i].address)
						{
							reservation_stations.entries[i].address = reservation_stations.entries[i].address + reservation_stations.entries[i].value1;
							rob.entries[reservation_stations.entries[i].destination].state = EXECUTE;
							reservation_stations.entries[i].value2 = rob.entries[j].value;
							rob.entries[reservation_stations.entries[i].destination].store_bypassed = true;
							pending_instructions.entries[reservation_stations.entries[i].destination].exe = clock_cycles;
						}
					}
				}
			}
		}
	}

	cout << "Past execution";
	//Write Results Stage
	for (int i = 0; i < num_units; i++) //this loop looks for ready values
	{
		if (exec_units[i].pc != UNDEFINED && exec_units[i].busy == 0)
		{
			for (int j = 0; j < rob.num_entries; j++) //this loop searches for ROB entries corresponding to the PC instruction on the execution unit
			{
				if (exec_units[i].pc == rob.entries[j].pc && rob.entries[j].pc != UNDEFINED && instr_memory[(exec_units[i].pc - instr_base_address) / 0x00000004].opcode != SWS)
				{
					rob.entries[j].value = exec_units[i].ALUoutput;
					rob.entries[j].state = WRITE_RESULT;
					pending_instructions.entries[j].wr = clock_cycles;
					for (int x = 0; x < reservation_stations.num_entries; x++) //this loop updates the reservation station entries
					{
						if (reservation_stations.entries[x].tag1 == j) //replacing the tag with the value for value 1 in all reservation station entries
						{
							reservation_stations.entries[x].value1 = exec_units[i].ALUoutput;
							reservation_stations.entries[x].tag1 = UNDEFINED;
						}
						if (reservation_stations.entries[x].tag2 == j) //replacing the tag with the value for value 2 in all reservation station entries
						{
							reservation_stations.entries[x].value2 = exec_units[i].ALUoutput;
							reservation_stations.entries[x].tag2 = UNDEFINED;
						}
						if (reservation_stations.entries[x].pc == exec_units[i].pc) //this is to clear the instruction from the reservation station
						{
							res_station_entry_t *ptr = &reservation_stations.entries[x];
							clean_res_station(ptr);
						}
					}
					exec_units[i].ALUoutput = UNDEFINED;
					exec_units[i].pc = UNDEFINED;
					loadReleasedUnit = i;
				}
			}
		}
	}
	//Write Results secion for STORE
	for (int i = 0; i < rob.num_entries; i++)
	{
		if (rob.entries[i].pc != UNDEFINED)
		{
			if (instr_memory[(rob.entries[i].pc - instr_base_address) / 0x00000004].opcode == SWS && rob.entries[i].state == EXECUTE && pending_instructions.entries[i].exe < clock_cycles)
			{
				for (int j = 0; j < reservation_stations.num_entries; j++)
				{
					if (reservation_stations.entries[j].pc == rob.entries[i].pc)
					{
						rob.entries[i].value = reservation_stations.entries[j].value1;
						rob.entries[i].state = WRITE_RESULT;
						pending_instructions.entries[i].wr = clock_cycles;
						res_station_entry_t *ptr = &reservation_stations.entries[j];
						clean_res_station(ptr);
					}
				}
			}
		}
	}
	//Write Results for STORE bypassed Loads
	for (int i = 0; i < reservation_stations.num_entries; i++)
	{
		if (reservation_stations.entries[i].pc != UNDEFINED)
		{
			if ((instr_memory[(reservation_stations.entries[i].pc - instr_base_address) / 0x00000004].opcode == LWS || instr_memory[(reservation_stations.entries[i].pc - instr_base_address) / 0x00000004].opcode == LW) && rob.entries[reservation_stations.entries[i].destination].store_bypassed == true && pending_instructions.entries[reservation_stations.entries[i].destination].exe < clock_cycles)
			{
				rob.entries[reservation_stations.entries[i].destination].value = reservation_stations.entries[i].value2;
				pending_instructions.entries[reservation_stations.entries[i].destination].wr = clock_cycles;
				rob.entries[reservation_stations.entries[i].destination].state = WRITE_RESULT;
				for (int x = 0; x < reservation_stations.num_entries; x++) //this loop updates the reservation station entries
				{
					if (reservation_stations.entries[x].pc != UNDEFINED)
					{
						if (reservation_stations.entries[x].tag1 == reservation_stations.entries[i].destination) //replacing the tag with the value for value 1 in all reservation station entries
						{
							reservation_stations.entries[x].value1 = rob.entries[reservation_stations.entries[i].destination].value;
							reservation_stations.entries[x].tag1 = UNDEFINED;
						}
						if (reservation_stations.entries[x].tag2 == reservation_stations.entries[i].destination) //replacing the tag with the value for value 2 in all reservation station entries
						{
							reservation_stations.entries[x].value2 = rob.entries[reservation_stations.entries[i].destination].value;
							reservation_stations.entries[x].tag2 = UNDEFINED;
						}
					}
				}
				res_station_entry_t *ptr = &reservation_stations.entries[i];
				clean_res_station(ptr);
			}
		}
	}

	//Commit Stage
	cout << "Entering Commit";

	for (int i = 0; i < rob.num_entries; i++)
	{

		bool dontCommit = false;
		if (rob.entries[i].ready == true)
		{
			// Checking if there are earlier instructions that we should wait for
			for (int j = 0; j < rob.num_entries; j++)
			{
				if (rob.entries[j].pc < rob.entries[i].pc)
				{
					dontCommit = true;
				}
			}
			if (dontCommit == false)
			{
				if (!is_branch(instr_memory[(rob.entries[i].pc - instr_base_address) / 0x00000004].opcode) && instr_memory[(rob.entries[i].pc - instr_base_address) / 0x00000004].opcode != SWS)
				{
					if (is_fp_alu(instr_memory[(rob.entries[i].pc - instr_base_address) / 0x00000004].opcode) || instr_memory[(rob.entries[i].pc - instr_base_address) / 0x00000004].opcode == LWS)
					{
						set_fp_register(rob.entries[i].destination - NUM_GP_REGISTERS, unsigned2float(rob.entries[i].value));
						if (i == FP_tags[rob.entries[i].destination - NUM_GP_REGISTERS]) //This is so that it doesn't delete other instruction's tags
						{
							FP_tags[rob.entries[i].destination - NUM_GP_REGISTERS] = UNDEFINED;
						}
					}
					else
					{
						set_int_register(rob.entries[i].destination, rob.entries[i].value);
						if (i == INT_tags[rob.entries[i].destination])
						{
							INT_tags[rob.entries[i].destination] = UNDEFINED;
						}
					}

					rob.entries[i].state = COMMIT;
					pending_instructions.entries[i].commit = clock_cycles;
					commit_to_log(pending_instructions.entries[i]);
					instr_window_entry_t *ptr = &pending_instructions.entries[i];
					clean_instr_window(ptr);
					rob_entry_t *ptr1 = &rob.entries[i];
					clean_rob(ptr1);
					instructions_executed++;
					goto AFTER_COMMIT;
				}
				if (is_branch(instr_memory[(rob.entries[i].pc - instr_base_address) / 0x00000004].opcode))
				{ //branch commit section
					if (rob.entries[i].value == rob.entries[i].pc + 4)
					{
						rob.entries[i].state = COMMIT;
						pending_instructions.entries[i].commit = clock_cycles;
						commit_to_log(pending_instructions.entries[i]);
						instr_window_entry_t *ptr = &pending_instructions.entries[i];
						clean_instr_window(ptr);
						rob_entry_t *ptr1 = &rob.entries[i];
						clean_rob(ptr1);
						instructions_executed++;
						goto AFTER_COMMIT;
					}
					else if (rob.entries[i].value != rob.entries[i].pc + 4)
					{
						PC = rob.entries[i].value;
						willBranch = true;
						rob.entries[i].state = COMMIT;
						pending_instructions.entries[i].commit = clock_cycles;
						commit_to_log(pending_instructions.entries[i]);
						instr_window_entry_t *ptr = &pending_instructions.entries[i];
						clean_instr_window(ptr);
						rob_entry_t *ptr1 = &rob.entries[i];
						clean_rob(ptr1);
						//rob flushed
						for (int i = 0; i < rob.num_entries; i++)
						{
							rob_entry_t *ptr = &rob.entries[i];
							clean_rob(ptr);
						}
						//reservation_stations flushed
						for (int i = 0; i < reservation_stations.num_entries; i++)
						{
							res_station_entry_t *ptr = &reservation_stations.entries[i];
							clean_res_station(ptr);
						}
						//execution units flushed
						for (int i = 0; i < num_units; i++)
						{
							cout << "It's inside the exec flush";
							exec_units[i].ALUoutput = UNDEFINED;
							exec_units[i].pc = UNDEFINED;
							exec_units[i].busy = 0;
						}
						//Tags flushed
						for (int i = 0; i < NUM_GP_REGISTERS; i++)
						{
							FP_tags[i] = UNDEFINED;
							INT_tags[i] = UNDEFINED;
						}
						ROBentryIndex = 0;

						unsigned minimum = 0; //This is to enter the pending instruction logs in sorted PC order
						int theIndex;
						while (minimum != UNDEFINED)
						{
							minimum = UNDEFINED;
							theIndex = UNDEFINED;
							for (int x = 0; x < pending_instructions.num_entries; x++)
							{
								if (pending_instructions.entries[x].pc < minimum)
								{
									minimum = pending_instructions.entries[x].pc;
									theIndex = x;
								}
							}
							if (theIndex != UNDEFINED && minimum != UNDEFINED)
							{
								commit_to_log(pending_instructions.entries[theIndex]);
								instr_window_entry_t *ptr = &pending_instructions.entries[theIndex];
								clean_instr_window(ptr);
							}
						}
						instructions_executed++;
						goto AFTER_COMMIT;
					}
				}
				if (instr_memory[(rob.entries[i].pc - instr_base_address) / 0x00000004].opcode == SWS && get_free_unit(instr_memory[(rob.entries[i].pc - instr_base_address) / 0x00000004].opcode) != UNDEFINED && rob.entries[i].state == WRITE_RESULT)
				{
					if (loadReleasedUnit != get_free_unit(instr_memory[(rob.entries[i].pc - instr_base_address) / 0x00000004].opcode))
					{
						write_memory(rob.entries[i].destination, rob.entries[i].value);
						rob.entries[i].state = COMMIT;
						instructions_executed++;
						pending_instructions.entries[i].commit = clock_cycles;
						commit_to_log(pending_instructions.entries[i]);
						int storeExecUnit = get_free_unit(instr_memory[(rob.entries[i].pc - instr_base_address) / 0x00000004].opcode);
						exec_units[storeExecUnit].pc = rob.entries[i].pc;
						exec_units[storeExecUnit].busy = exec_units[storeExecUnit].latency;
						/*for (int j = 0; j < reservation_stations.num_entries; j++)
						{
							if (reservation_stations.entries[j].pc != UNDEFINED)
							{
								if (instr_memory[(rob.entries[reservation_stations.entries[j].destination].pc - instr_base_address) / 0x00000004].opcode == LWS && rob.entries[reservation_stations.entries[j].destination].state == ISSUE && reservation_stations.entries[j].address + reservation_stations.entries[j].value1 == rob.entries[i].destination)
								{
									/*reservation_stations.entries[j].address = reservation_stations.entries[j].address + reservation_stations.entries[j].value1;
									rob.entries[reservation_stations.entries[j].destination].state = EXECUTE;
									reservation_stations.entries[j].value2 = rob.entries[i].value;
									pending_instructions.entries[reservation_stations.entries[j].destination].exe = clock_cycles;
									//goto AFTER_COMMIT;
								}
							}
						}*/
					}
				}
			}
		}
	}

AFTER_COMMIT:

	for (int i = 0; i < rob.num_entries; i++)
	{
		if (pending_instructions.entries[i].wr != UNDEFINED)
		{
			rob.entries[i].ready = true;
		}
	}

	decrement_units_busy_time();
	//debug_units();
	if (instr_memory[(PC - instr_base_address) / 0x00000004].opcode != EOP && issue_struct_stall == false && willBranch == false)
	{
		PC += 0x00000004;
	}
	for (int i = 0; i < num_units; i++)
	{
		if (exec_units[i].pc != UNDEFINED)
		{
			if (instr_memory[(exec_units[i].pc - instr_base_address) / 0x00000004].opcode == SWS && exec_units[i].busy == 0)
			{
				for (int y = 0; y < rob.num_entries; y++)
				{
					if (rob.entries[y].pc == exec_units[i].pc)
					{
						exec_units[i].pc = UNDEFINED;
						instr_window_entry_t *ptr = &pending_instructions.entries[y];
						clean_instr_window(ptr);
						rob_entry_t *ptr1 = &rob.entries[y];
						clean_rob(ptr1);
						//instructions_executed++;
						//goto AFTER_COMMIT;
					}
				}
			}
		}
	}
	cout << dec << " \n The number of clock cycles are:" << static_cast<int>(clock_cycles) << "\n";
	cout << dec << " \n The instructions executed are:" << static_cast<int>(instructions_executed) << "\n";
	//print_pending_instructions();
	//print_rob();
	clock_cycles++;
	if (cycles == NULL)
	{
		int notEmptyEntries = 0;
		for (int i = 0; i < rob.num_entries; i++)
		{
			if (rob.entries[i].pc != UNDEFINED)
			{
				notEmptyEntries++;
			}
		}
		if (notEmptyEntries > 0 || instr_memory[(PC - instr_base_address) / 0x00000004].opcode != EOP)
		{
			if (clock_cycles == 600)
			{
				//return;
			}
			run();
		}
	}
}

//reset the state of the simulator - please complete
void sim_ooo::reset()
{

	//init instruction log
	init_log();

	// data memory
	for (unsigned i = 0; i < data_memory_size; i++)
		data_memory[i] = 0xFF;

	//instr memory
	for (int i = 0; i < PROGRAM_SIZE; i++)
	{
		instr_memory[i].opcode = (opcode_t)EOP;
		instr_memory[i].src1 = UNDEFINED;
		instr_memory[i].src2 = UNDEFINED;
		instr_memory[i].dest = UNDEFINED;
		instr_memory[i].immediate = UNDEFINED;
	}

	//general purpose registers
	for (int i = 0; i < NUM_GP_REGISTERS; i++)
	{
		FP_regs[i] = UNDEFINED;
		INT_regs[i] = UNDEFINED;
		INT_tags[i] = UNDEFINED;
		FP_tags[i] = UNDEFINED;
	}
	ROBentryIndex = 0;

	//rob
	for (int i = 0; i < rob.num_entries; i++)
	{
		rob_entry_t *ptr = &rob.entries[i];
		clean_rob(ptr);
	}
	//reservation_stations
	for (int i = 0; i < reservation_stations.num_entries; i++)
	{
		res_station_entry_t *ptr = &reservation_stations.entries[i];
		clean_res_station(ptr);
	}
	//pending_instructions
	for (int i = 0; i < pending_instructions.num_entries; i++)
	{
		instr_window_entry_t *ptr = &pending_instructions.entries[i];
		clean_instr_window(ptr);
	}

	//execution statistics
	clock_cycles = 0;
	instructions_executed = 0;
	issue_struct_stall = false;
	vacantPlace = false;

	//other required initializations
}

//taken from project 1 fp sim
void sim_ooo::decrement_units_busy_time()
{
	for (unsigned u = 0; u < num_units; u++)
	{
		if (exec_units[u].busy > 0)
			exec_units[u].busy--;
	}
}

void sim_ooo::debug_units()
{
	for (unsigned u = 0; u < num_units; u++)
	{
		cout << " -- unit " << exec_units[u].type << " latency=" << exec_units[u].latency << dec << " busy=" << exec_units[u].busy << " PC= " << hex << exec_units[u].pc << endl;
	}
}

/* registers related */

int sim_ooo::get_int_register(unsigned reg)
{
	return INT_regs[reg]; //please modify
}

void sim_ooo::set_int_register(unsigned reg, int value)
{
	INT_regs[reg] = value;
}

float sim_ooo::get_fp_register(unsigned reg)
{
	return FP_regs[reg]; //please modify
}

void sim_ooo::set_fp_register(unsigned reg, float value)
{
	FP_regs[reg] = value;
}

unsigned sim_ooo::get_int_register_tag(unsigned reg)
{
	return INT_tags[reg]; //please modify
}

unsigned sim_ooo::get_fp_register_tag(unsigned reg)
{
	return FP_tags[reg]; //please modify
}
