#ifndef MVBONCE_MVB_DEF_H
#define MVBONCE_MVB_DEF_H
//=============================================================================
//
//      mvb_def.h
//
//      ARM Pin configuration, GPIO definitions and EXTI configuration
//      Macros for hardware abstraction layer calls
//
//=============================================================================
//#####DESCRIPTIONBEGIN####
//
// Author(s):   Yinlong Su
// Date:        2012-08-16
// Modified:	2012-10-22
// Description: MVB basic data structure definition
// Version:     1.0
// Usage:       #include "mvb_def.h"
//
//####DESCRIPTIONEND####
//
//=============================================================================

/* ==========================================================================
 *
 *  F_code mapping
 *
 * ==========================================================================
 */
#define	FRAME_F_CODE_0	0	// Process Data (size: 16bits)
#define	FRAME_F_CODE_1	1	// Process Data (size: 32bits)
#define	FRAME_F_CODE_2	2	// Process Data (size: 64bits)
#define	FRAME_F_CODE_3	3	// Process Data (size:128bits)
#define	FRAME_F_CODE_4	4	// Process Data (size:256bits)
#define	FRAME_F_CODE_5	5	// reserved
#define	FRAME_F_CODE_6	6	// reserved
#define	FRAME_F_CODE_7	7	// reserved
#define	FRAME_F_CODE_8	8	// Mastership_Transfer (size:16bits||source:proposed master||destination:master)
#define	FRAME_F_CODE_9	9
#define	FRAME_F_CODE_10	10	// reserved
#define	FRAME_F_CODE_11	11	// reserved
#define	FRAME_F_CODE_12	12
#define	FRAME_F_CODE_13	13
#define	FRAME_F_CODE_14	14
#define	FRAME_F_CODE_15	15	// Device_status (size:16bits||source:single device||destination:master or monitor device)

#define FRAME_F_CODE(__content) (((__content) & 0xF000) >> 12)
#define FRAME_ADDRESS(__content) (__content & 0x0FFF)

/* ==========================================================================
 *
 *  BA states
 *
 * ==========================================================================
 */
#define BA_STATES_STANDBY_MASTER	0
#define BA_STATES_REGULAR_MASTER	1
#define BA_STATES_FIND_NEXT			2
#define BA_STATES_INTERIM_MASTER	3


/* ==========================================================================
 *
 *  Constants
 *
 * ==========================================================================
 */
#define uint16_t unsigned short
#define uint32_t unsigned int

#define UINT unsigned short
/* --------------------------------------------------------------------------
 *  NOTE:
 *  The obvious few that compilers may define for you.
 *  But in case they don't:
 * --------------------------------------------------------------------------
 */
#ifndef NULL
#   define NULL     (0)
#endif

#ifndef TRUE
#   define TRUE     (1==1)
#endif

#ifndef FALSE
#   define FALSE    (!TRUE)
#endif


/* ==========================================================================
 *
 *  Data Types
 *
 * ==========================================================================
 */

/* --------------------------------------------------------------------------
 *  Constants for basic data types (8, 16, 32 and 64 bits)
 * --------------------------------------------------------------------------
 */
#ifndef MVB_DEF_BASE_TYPE8
#   define MVB_DEF_BASE_TYPE8   char
#endif
#ifndef MVB_DEF_BASE_TYPE16
#   define MVB_DEF_BASE_TYPE16  short
#endif
#ifndef MVB_DEF_BASE_TYPE32
#   define MVB_DEF_BASE_TYPE32  long
#endif
#ifndef MVB_DEF_BASE_TYPE64
#   define MVB_DEF_BASE_TYPE64  long long
#endif

/* --------------------------------------------------------------------------
 *  Data types with less than 8-bits
 * --------------------------------------------------------------------------
 */
typedef unsigned MVB_DEF_BASE_TYPE8     BOOLEAN1;
typedef unsigned MVB_DEF_BASE_TYPE8     ANTIVALENT2;
typedef unsigned MVB_DEF_BASE_TYPE8     BCD4;
typedef unsigned MVB_DEF_BASE_TYPE8     ENUM4;

/* --------------------------------------------------------------------------
 *  8-bit data types
 * --------------------------------------------------------------------------
 */
typedef unsigned MVB_DEF_BASE_TYPE8     BITSET8;
typedef unsigned MVB_DEF_BASE_TYPE8     WORD8;
typedef unsigned MVB_DEF_BASE_TYPE8     ENUM8;
typedef unsigned MVB_DEF_BASE_TYPE8     UNSIGNED8;
typedef   signed MVB_DEF_BASE_TYPE8     INTEGER8;
typedef          MVB_DEF_BASE_TYPE8     CHARACTER8;

/* --------------------------------------------------------------------------
 *  16-bit data types
 * --------------------------------------------------------------------------
 */
typedef unsigned MVB_DEF_BASE_TYPE16    BITSET16;
typedef unsigned MVB_DEF_BASE_TYPE16    WORD16;
typedef unsigned MVB_DEF_BASE_TYPE16    ENUM16;
typedef unsigned MVB_DEF_BASE_TYPE16    UNSIGNED16;
typedef   signed MVB_DEF_BASE_TYPE16    INTEGER16;
typedef unsigned MVB_DEF_BASE_TYPE16    BIPOLAR2_16;
typedef unsigned MVB_DEF_BASE_TYPE16    UNIPOLAR2_16;
typedef unsigned MVB_DEF_BASE_TYPE16    BIPOLAR4_16;

/* --------------------------------------------------------------------------
 *  32-bit data types
 * --------------------------------------------------------------------------
 */
typedef	         float                  REAL32;
typedef unsigned MVB_DEF_BASE_TYPE32    BITSET32;
typedef unsigned MVB_DEF_BASE_TYPE32    WORD32;
typedef unsigned MVB_DEF_BASE_TYPE32    ENUM32;
typedef unsigned MVB_DEF_BASE_TYPE32    UNSIGNED32;
typedef   signed MVB_DEF_BASE_TYPE32    INTEGER32;

/* --------------------------------------------------------------------------
 *  64-bit data types
 * --------------------------------------------------------------------------
 */
typedef unsigned MVB_DEF_BASE_TYPE64    BITSET64;
typedef unsigned MVB_DEF_BASE_TYPE64    WORD64;
typedef unsigned MVB_DEF_BASE_TYPE64    ENUM64;
typedef unsigned MVB_DEF_BASE_TYPE64    UNSIGNED64;
typedef   signed MVB_DEF_BASE_TYPE64    INTEGER64;

/* --------------------------------------------------------------------------
 *  Structured data types
 * --------------------------------------------------------------------------
 */
#define MVB_SIZEOF_STRUCT_BITSET256 32
typedef struct
{
    BITSET8     byte[32];
}   BITSET256;

#define MVB_SIZEOF_STRUCT_TIMEDATE48 8
typedef struct
{
    UNSIGNED32  seconds;
    UNSIGNED16  ticks;
}   TIMEDATE48;

#define MVB_SIZEOF_STRUCT_STRING32 32
typedef struct
{
    CHARACTER8  character[32];
}   STRING32;

/* --------------------------------------------------------------------------
 *  Special data type - BITFIELD16
 *  NOTE:
 *  16-bit data type used to build structured types like DS_NAME,
 *  PV_NAME, SV_MVB_DEVICE_STATUS.
 *  This will result in structured types, which size are multiplies
 *  of 16-bits.
 * --------------------------------------------------------------------------
 */
#ifndef MVB_DEF_BITFIELD16
#define MVB_DEF_BITFIELD16   UNSIGNED16
#endif
typedef MVB_DEF_BITFIELD16      BITFIELD16;



/************************************************************************/
/*                                                                      */
/*  Global Structures Declaration                                       */
/*                                                                      */
/************************************************************************/
#define MAX_NUMBER_OF_BIN_ENTRIES   64    // 4 Entries per MVB, max 16 MVBs
#define LENGTH_OF_PROJECT_STRINGS   16    // 16 chars for Project strings
#define PORTADDRESS_MASK 0x0FFF
#define FCODE_MASK 0xF000
#define SRC_MASK 0x0800
#define SNK_MASK 0x0400
#define BA_MASK 0xA0
#define LINE_MASK 0x0C

/************************************************************************/
/*  Header                                                              */
/************************************************************************/
typedef struct Header {
	unsigned short  checksum;
	unsigned long   reserved1;
	unsigned long   size;
	unsigned long   reserved2;
	unsigned long   reserved3;
	//unsigned long   header_size;
	char            project_name[16];
	char            project_version[16];
	char            project_date[16];
	unsigned short  nr_entries;
	unsigned long   entry_offset[MAX_NUMBER_OF_BIN_ENTRIES];
	//unsigned long   entry_size[MAX_NUMBER_OF_BIN_ENTRIES];
}   HEADER;
/************************************************************************/
/*  Mvb_Control                                                         */
/************************************************************************/
typedef struct Mvb_Control {
	unsigned char bus_id;
	unsigned char reserverd1;
	unsigned short device_address;
	unsigned char reserverd2;
	unsigned char t_ignore;
	unsigned char reserverd3;
	unsigned char code;
	
}   MVB_CONTROL;

/************************************************************************/
/*  MVB_Administrator                                                   */
/************************************************************************/
typedef struct MVB_Administrator {
	unsigned char bus_id;
	unsigned char reserved1;
	unsigned short checkword0;
	unsigned short configuration_version;
	unsigned short t_reply_max;
	unsigned short macro_cycles;
	unsigned short event_poll_strategy;
	unsigned short basic_period;
	unsigned short macrocycles_per_turn;
	unsigned short devices_scan_strategy ;
	unsigned short reserved2;
	unsigned short reserved3;
	unsigned short reserved4;
	unsigned short reserved5;
	unsigned short known_devices_list_offset;
	unsigned short reserved_list_offset;
	unsigned short periodic_list_offset;
	unsigned short bus_administrators_list_offset;
	unsigned short devices_scan_list_offset;
	unsigned short end_list_offset;

	unsigned short * known_devices_list;
	unsigned short cycle_lists_offsets [11];
	unsigned short cycle_lists_size [11];
	unsigned short split_lists_offsets [5];
	//11 cycle lists
	unsigned short * cycle_lists [11];
	//unsigned short * cycle_1;
	//unsigned short * cycle_2;
	//unsigned short * cycle_4;
	//unsigned short * cycle_8;
	//unsigned short * cycle_16;
	//unsigned short * cycle_32;
	//unsigned short * cycle_64;
	//unsigned short * cycle_128;
	//unsigned short * cycle_256;
	//unsigned short * cycle_512;
	//unsigned short * cycle_1024;
	//split lists 10(5 * 2) 分开了，否则需要用short读取，进行大小端转换
	unsigned char  split_2		[4];
	unsigned char  split_4		[4];
	unsigned char  split_8		[16];
	unsigned char  split_16		[16];
	unsigned char  split_32		[64];
	unsigned char  split_64		[64];
	unsigned char  split_128	[256];
	unsigned char  split_256	[256];
	unsigned char  split_512	[1024];
	unsigned char  split_1024	[1024];
	//bus administrators list
	unsigned short * bus_administrators_list;
	unsigned char * device_scan_list_count0;
	unsigned char * device_scan_list_count1;
}MVB_ADMINISTRATOR;

#define DEVICES_SCAN_STRATEGY_ENUM_KNOWN		0
#define DEVICES_SCAN_STRATEGY_ENUM_ALL			1

/************************************************************************/
/*  ports_configuration                                                 */
/************************************************************************/
typedef struct Ports_Configuration {
	unsigned short nr_ports;
	unsigned short * ports_info_0;
	unsigned short * ports_info_1;
}PORTS_CONFIGURATION;

/************************************************************************/
/*  Md_control                                                          */
/************************************************************************/
typedef struct Md_Control {
	unsigned short max_call_number;
	unsigned short max_inst_number;
	unsigned short default_reply_timeout;
	unsigned char reserverd1;
	unsigned char my_credit;
}MD_CONTROL;

/************************************************************************/
/*  Function_directory                                                  */
/************************************************************************/
typedef struct Function_Directory {
	unsigned char clear_directory;
	unsigned char nr_functions;
	unsigned char * function_id;
	unsigned char * station_id;
}FUNCTION_DIRECTORY;

/************************************************************************/
/*  MVB_DEVICE_STATUS                                                   */
/************************************************************************/
#define MVB_SIZEOF_STRUCT_MVB_DEVICE_STATUS 2
typedef struct
{
	/* common flags */
	BITFIELD16  ser : 1;
	BITFIELD16  dnr : 1;
	BITFIELD16  frc : 1;
	BITFIELD16  erd : 1;
	BITFIELD16  sdd : 1;
	BITFIELD16  ssd : 1;
	BITFIELD16  rld : 1;
	BITFIELD16  lat : 1;
	/* class specific */
	BITFIELD16  cs3 : 1;
	BITFIELD16  cs2 : 1;
	BITFIELD16  cs1 : 1;
	BITFIELD16  cs0 : 1;
	/* capabilities */
	BITFIELD16  md  : 1;
	BITFIELD16  gw  : 1;
	BITFIELD16  ba  : 1;
	BITFIELD16  sp  : 1;
} MVB_DEVICE_STATUS;

/* --------------------------------------------------------------------------
 *  Bit Constants : SV_MVB_DEVICE_STATUS_BIT_xxx
 *
 *  Purpose       : MVB device status.
 * --------------------------------------------------------------------------
 */
/* capabilities */
#define MVB_DEVICE_STATUS_BIT_SP  0x8000 /* special device (class1=0)   */
#define MVB_DEVICE_STATUS_BIT_BA  0x4000 /* bus administrator           */
#define MVB_DEVICE_STATUS_BIT_GW  0x2000 /* gateway                     */
#define MVB_DEVICE_STATUS_BIT_MD  0x1000 /* message data                */

/* class specific (general) */
#define MVB_DEVICE_STATUS_BIT_CS0 0x0800 /* first  bit ...  ...of       */
#define MVB_DEVICE_STATUS_BIT_CS1 0x0400 /* second bit ...    class     */
#define MVB_DEVICE_STATUS_BIT_CS2 0x0200 /* third  bit ...   specific   */
#define MVB_DEVICE_STATUS_BIT_CS3 0x0100 /* fourth bit ...    field     */

/* class specific (bus administrator) */
#define MVB_DEVICE_STATUS_BIT_AX1 0x0800 /* second last significant bit */
                                            /*  of the actualisation key   */
                                            /*  of the periodic list       */
#define MVB_DEVICE_STATUS_BIT_AX0 0x0400 /* least significant bit of    */
                                            /*  the actualisation key of   */
                                            /*  the periodic list          */
#define MVB_DEVICE_STATUS_BIT_ACT 0x0200 /* device is actualised and in */
                                            /*  condition of becoming      */
                                            /* master                      */
#define MVB_DEVICE_STATUS_BIT_MAS 0x0100 /* device is the current       */
                                            /*  master                     */

/* class specific (gateway without bus administrator capability) */
#define MVB_DEVICE_STATUS_BIT_STD 0x0800 /* static disturbance          */
#define MVB_DEVICE_STATUS_BIT_DYD 0x0400 /* dynamic disturbance         */

/* common flags */
#define MVB_DEVICE_STATUS_BIT_LAT 0x0080 /* line A trusted              */
#define MVB_DEVICE_STATUS_BIT_RLD 0x0040 /* redundant line disturbed    */
#define MVB_DEVICE_STATUS_BIT_SSD 0x0020 /* some system disturbance     */
#define MVB_DEVICE_STATUS_BIT_SDD 0x0010 /* some device disturbance     */
#define MVB_DEVICE_STATUS_BIT_ERD 0x0008 /* extended reply delay        */
#define MVB_DEVICE_STATUS_BIT_FRC 0x0004 /* forced device               */
#define MVB_DEVICE_STATUS_BIT_DNR 0x0002 /* device not ready            */
#define MVB_DEVICE_STATUS_BIT_SER 0x0001 /* system reserved             */
#endif // ifndef MVBONCE_MVB_DEF_H