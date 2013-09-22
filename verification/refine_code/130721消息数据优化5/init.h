#ifndef MVBONCE_INIT_H
#define MVBONCE_INIT_H
//=============================================================================
//
//      init.h
//
//      Init header
//
//=============================================================================
//#####DESCRIPTIONBEGIN####
//
// Author(s):   Yinlong Su
// Date:        2012-11-21
// Modified:	2012-11-21
// Description: Init header
// Version:     1.0
// Usage:       #include "init.h"
//
//####DESCRIPTIONEND####
//
//=============================================================================
#include "mvb_project.h"
#include "mvb_def.h"
#include "hal.h"
#include <cyg/kernel/kapi.h>
#include <cyg/fileio/fileio.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define LITTLE_ENDIAN
#define uint16_t unsigned short
#define uint32_t unsigned int

#if defined(BIG_ENDIAN) && !defined(LITTLE_ENDIAN)

#define htons(A) (A)
#define htonl(A) (A)
#define ntohs(A) (A)
#define ntohl(A) (A)

#elif defined(LITTLE_ENDIAN) && !defined(BIG_ENDIAN)

#define htons(A) ((((uint16_t)(A) & 0xff00) >> 8 ) | \
	(((uint16_t)(A) & 0x00ff) << 8 ))
#define htonl(A) ((((uint32_t)(A) & 0xff000000) >> 24) | \
	(((uint32_t)(A) & 0x00ff0000) >> 8 ) | \
	(((uint32_t)(A) & 0x0000ff00) << 8 ) | \
	(((uint32_t)(A) & 0x000000ff) << 24))
#define ntohs     htons
#define ntohl     htonl
#endif

/************************************************************************/
/*  Bin-Files                                                           */
/************************************************************************/

#define CYGNUM_FS_ROM_BASE_ADDRESS 0x08020000
MTAB_ENTRY( romfs_mte1,
                   "/",
                   "romfs",
                   "",
                   (CYG_ADDRWORD) CYGNUM_FS_ROM_BASE_ADDRESS );

int fpga();
int parse();
void create_structure();

#endif // ifndef MVBONCE_INIT_H
