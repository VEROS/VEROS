#ifndef MVBONCE_MVB_PROJECT_H
#define MVBONCE_MVB_PROJECT_H
//=============================================================================
//
//      mvb_project.h
//
//      MVB project configuration
//
//=============================================================================
//#####DESCRIPTIONBEGIN####
//
// Author(s):   Yinlong Su
// Date:        2012-08-20
// Description: MVB project header configuration
// Version:     1.0
// Usage:       #include "mvb_project.h"
//
//####DESCRIPTIONEND####
//
//=============================================================================

// MVB HAL_IO Version
//#define MVBPROJ_HAL_IO_V1
//#define MVBPROJ_HAL_IO_V4
//#define MVBPROJ_HAL_IO_V7A
#define MVBPROJ_HAL_IO_V8

// MVB support switch
#define MVBPROJ_BASIC_INFO_SUPPORT
#define MVBPROJ_LED_SUPPORT

// MVB function block switch
//#define MVBPROJ_INIT_FPGA_BLOCKED
//#define MVBPROJ_INIT_FPGA_TRANS_BLOCKED
//#define MVBPROJ_INIT_BIN_BLOCKED
//#define MVBPROJ_INIT_BIN_TRANS_BLOCKED
//#define MVBPROJ_DEVICES_SCAN_BLOCKED
//#define MVBPROJ_BUILD_DEVICES_LIST_BLOCKED
#define MVBPROJ_MASTERSHIP_TRANSFER_BLOCKED
//#define MVBPROJ_ARBITRATION_BLOCKED

// MVB forced default setting
//#define MVBPROJ_DEFAULT_ADDRESS 0x21
//#define MVBPROJ_DEFAULT_MASTER_ADDRESS 0x05
#define MVBPROJ_DEFAULT_DEVICES_SCAN_STRATEGY DEVICES_SCAN_STRATEGY_ENUM_ALL
#define MVBPROJ_DEFAULT_SCAN_UNIT 1
#define MVBPROJ_DEFAULT_BA_MAX_BASIC_PERIOD 1024*16

//#define MVBPROJ_DEFAULT_EMPTY_MAINFRAME
//#define MVBPROJ_DEFAULT_EMPTY_PORTCONFIG

//#define MVBPROJ_ROLE_MASTER
//#define MVBPROJ_ROLE_SLAVE

// MVB default KDL setting
//#define MVBPROJ_DEFAULT_KDL_V1
//#define MVBPROJ_DEFAULT_KDL_V2
#define MVBPROJ_DEFAULT_KDL_V3

// MVB debug info output switch (printf only)
//#define MVBPROJ_DEBUG_INFO
//#define MVBPROJ_DEBUG_REALTIME
//#define MVBPROJ_DEBUG_CONN_BA
//#define MVBPROJ_DEBUG_SYNC

//-----------------------------------------------------------------------------
// end of mvb_project.h
#endif // ifndef MVBONCE_MVB_PROJECT_H