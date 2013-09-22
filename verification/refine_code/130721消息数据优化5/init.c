//=============================================================================
//
//      init.c
//
//      Init c
//
//=============================================================================
//#####DESCRIPTIONBEGIN####
//
// Author(s):   Haichao Li, Qicong Lv, Yinlong Su
// Date:        2012-07-08
// Modified:	2012-11-09
// Description: Init c
// Version:     2.0
//
//####DESCRIPTIONEND####
//
//=============================================================================

#include "init.h"

//=============================================================================
// Variable Description
//
// * See data structure in mvb_def.h
// HEADER header :: See HEADER structure
// MVB_CONTROL mvb_control :: See MVB_CONTROL structure
// MVB_ADMINISTRATOR mvb_administrator :: See MVB_ADMINISTRATOR structure
// PORTS_CONFIGURATION ports_configuration :: See PORTS_CONFIGURATION structure
// MD_CONTROL md_control :: See MD_CONTROL structure
// FUNCTION_DIRECTORY function_directory :: See FUNCTION_DIRECTORY structure
// MVB_DEVICE_STATUS mvb_device_status :: See MVB_DEVICE_STATUS structure
// cyg_uint16 mvb_device_status_16 :: Copy of mvb-device_status as 16 bits word.
//
// * Flag: Whether binary file has certain part
// unsigned short MVB_CONTROL_FLAG
// unsigned short MVB_ADMINISTRATOR_FLAG
// unsigned short PORTS_CONFIGURATION_FLAG
// unsigned short MD_CONTROL_FLAG
// unsigned short FUNCTION_DIRECTORY_FLAG
//
// unsigned short this_akey :: Binary file configuration version
// unsigned short this_addr :: Binary file device address
HEADER					header;
MVB_CONTROL				mvb_control;
MVB_ADMINISTRATOR		mvb_administrator;
PORTS_CONFIGURATION		ports_configuration;
MD_CONTROL				md_control;
FUNCTION_DIRECTORY		function_directory;

MVB_DEVICE_STATUS		mvb_device_status;
cyg_uint16				mvb_device_status_16;

unsigned short MVB_CONTROL_FLAG;
unsigned short MVB_ADMINISTRATOR_FLAG;
unsigned short PORTS_CONFIGURATION_FLAG;
unsigned short MD_CONTROL_FLAG;
unsigned short FUNCTION_DIRECTORY_FLAG;

unsigned short this_akey;
unsigned short this_addr;

/* --------------------------------------------------------------------------
 *  fpga
 *
 *  FPGA initialization function
 *
 *  @param	: void
 *  @return	: int
 *              0 as failed
 *              1 as succeed
 *
 *  Refresh FPGA program
 * --------------------------------------------------------------------------
 */
int fpga()
{
#ifndef MVBPROJ_INIT_FPGA_BLOCKED

#ifdef MVBPROJ_BASIC_INFO_SUPPORT
	printf("...refreshing FPGA...\n");
#endif // ifdef MVBPROJ_BASIC_INFO_SUPPORT

	CYG_ADDRESS base;
	
	CYGHWR_HAL_STM32_GPIO_SET(HAL_IO_FPGA_CCLK);
	CYGHWR_HAL_STM32_GPIO_SET(HAL_IO_FPGA_INIT_B);
	CYGHWR_HAL_STM32_GPIO_SET(HAL_IO_FPGA_PROG_B);
	CYGHWR_HAL_STM32_GPIO_SET(HAL_IO_FPGA_PROG_DON);
	CYGHWR_HAL_STM32_GPIO_SET(HAL_IO_FPGA_DIN);

	int data;
	
	CYGHWR_HAL_STM32_GPIO_IN( HAL_IO_FPGA_INIT_B , &data );

	CYGHWR_HAL_STM32_GPIO_OUT( HAL_IO_FPGA_PROG_B, 0 );
	mvb_arm_delay(10000);
	CYGHWR_HAL_STM32_GPIO_OUT( HAL_IO_FPGA_PROG_B, 1 );
	mvb_arm_delay(10000);
	CYGHWR_HAL_STM32_GPIO_IN( HAL_IO_FPGA_INIT_B , &data );
	if ( !data)
		return 0;
		
	int err = mount("","/","romfs");
	
	FILE* fp = fopen( "fpga.bin" , "rb" );
	if( fp == NULL )
    {
#ifdef MVBPROJ_DEBUG_INFO
		printf("File open error!\n");
#endif
		return 0;
	}
	char buff;
	int i ;
	int mark;
	while( fread( &buff , 1 , 1 , fp ) )
	{
		for( i = 0 , mark = 1 ; i < 8 ; ++i )
		{
			CYGHWR_HAL_STM32_GPIO_OUT( HAL_IO_FPGA_DIN , buff & mark );
			CYGHWR_HAL_STM32_GPIO_OUT( HAL_IO_FPGA_CCLK , 0 );
			CYGHWR_HAL_STM32_GPIO_OUT( HAL_IO_FPGA_CCLK , 1 );
			mark <<= 1;
		}
	}
	fclose( fp );
	CYGHWR_HAL_STM32_GPIO_IN( HAL_IO_FPGA_PROG_DON , &data );
	if( !data )
		return 0;

#endif // ifndef MVBPROJ_INIT_FPGA_BLOCKED

	return 1;
}

/* --------------------------------------------------------------------------
 *  parse
 *
 *  Binary file parsing and transmitting
 *
 *  @param	: void
 *  @return	: int
 *              0 as failed
 *              1 as succeed
 *
 *  Parse binary file and transmit data
 * --------------------------------------------------------------------------
 */
int parse()
{
#ifndef MVBPROJ_INIT_BIN_BLOCKED

#ifdef MVBPROJ_BASIC_INFO_SUPPORT
	printf("...parsing binary file...\n");
#endif // ifdef MVBPROJ_BASIC_INFO_SUPPORT

	FILE * fp;
	unsigned short i;
	unsigned short j;
	unsigned short k;
	
	MVB_CONTROL_FLAG = 0;
	MVB_ADMINISTRATOR_FLAG = 0;
	PORTS_CONFIGURATION_FLAG = 0;
	MD_CONTROL_FLAG = 0;
	FUNCTION_DIRECTORY_FLAG = 0;

	int header_flag = 0;//header_standard
	int offset_P0 = 0;
	unsigned short offset_diff;
	unsigned short count;
	unsigned short sum;

	unsigned short * cursor ;//=(unsigned short*)malloc(sizeof(unsigned short)*1024);//[1024];
	unsigned short * main_frame ;//[1024][8];
	unsigned short * array ;//= (unsigned short*)malloc(sizeof(unsigned short)*1024);// [1024];

	unsigned short power [] = {1,2,4,8,16,32,64,128,256,512,1024};
	char buffer [32];
	//BIT *ports = (BIT*)malloc(sizeof(BIT)*1024);//[1024];
	//unsigned short port_address;
	//unsigned short port_helper;
	//unsigned short src_snk;
	unsigned short data;
	unsigned int data2;
	
	// for checksum calc
	unsigned short checksum_read;
	unsigned short checksum_calc;
	unsigned int size_read;
	unsigned int size_count;
	unsigned char value8;
		
	//char value [100];
	int err;
	err = mount("","/","romfs");

	char * filename = "device.bin";
	fp = fopen(filename,"rb");
	if (fp == NULL)
	{
#ifdef MVBPROJ_DEBUG_INFO
	printf("Failed to open file %s",filename);
#endif
		return 0;
	}
	
	// checksum calc
	fread(&checksum_read, sizeof(unsigned short), 1, fp);
	checksum_read = htons(checksum_read);
	size_count = 1;
	checksum_calc = 0;
	while (!feof(fp))
	{
		fread(&value8, sizeof(unsigned char), 1, fp);
		size_count++;
		checksum_calc = (unsigned short)(checksum_calc + value8);
	}
	if (checksum_read != checksum_calc)
	{
#ifdef MVBPROJ_BASIC_INFO_SUPPORT
		printf("checksum error.\n");
		printf("checksum read = 0x%04x, checksum calculated = 0x%04x, size count = 0x%08x\n", checksum_read, checksum_calc, size_count);
#endif // ifdef MVBPROJ_BASIC_INFO_SUPPORT
		return 0;
	}
	rewind(fp);
	fseek(fp, 2, SEEK_SET);
	fread(&data2, sizeof(unsigned int), 1, fp);
	data2 = htonl(data2);
	if (data2 == size_count)
	{
		header_flag = 0; // std
		size_read = size_count;
	}
	else
	{
		fseek(fp, 4, SEEK_SET);
		fread(&data2, sizeof(unsigned int), 1, fp);
		data2 = htonl(data2);
		if (data2 == size_count)
		{
			header_flag = 1; // ext
			size_read = size_count;
		}
		else
		{
#ifdef MVBPROJ_BASIC_INFO_SUPPORT
			printf("size error.\n");
			printf("size count = 0x%08x, size read = 0x%08x\n", size_count, data2);
#endif // ifdef MVBPROJ_BASIC_INFO_SUPPORT
			return 0;
		}
	}
	
	/*
	fread(buffer,1,16,fp);
	for(i = 8; i < 16; i++)
	{
		if(buffer[i] != 0)
		{
			break;
		}
	}
	if(i == 16) header_flag = 1;//head_extended;
	*/
	rewind(fp);
	if(header_flag == 0)//std
	{
		fread((unsigned short*)&header.checksum,sizeof(unsigned short),1,fp);
		header.checksum = htons(header.checksum);
		fread((unsigned long*)&header.size,sizeof(unsigned long),1,fp);
		header.size = htonl(header.size);
		fread(header.project_name,sizeof(char),16,fp);
		fread(header.project_version,sizeof(char),16,fp);
		fread(header.project_date,sizeof(char),16,fp);

	}
	else if(header_flag == 1)//ext
	{
		fread((unsigned short*)&header.checksum,sizeof(unsigned short),1,fp);
		header.checksum = htons(header.checksum);
		fread((unsigned short*)&header.reserved1,sizeof(unsigned short),1,fp);
		header.reserved1 = htons(header.reserved1);
		fread((unsigned long*)&header.size,sizeof(unsigned long),1,fp);
		header.size = htonl(header.size);
		fread((unsigned long*)&header.reserved2,sizeof(unsigned long),1,fp);
		header.reserved2 = htonl(header.reserved2);
		fread((unsigned long*)&header.reserved3,sizeof(unsigned long),1,fp);
		header.reserved3 = htonl(header.reserved3);
		fread(header.project_name,sizeof(char),16,fp);
		fread(header.project_version,sizeof(char),16,fp);
		fread(header.project_date,sizeof(char),16,fp);
	}
	fread((unsigned short*)&header.nr_entries,sizeof(unsigned short),1,fp);
	header.nr_entries = htons(header.nr_entries);
	for(i = 0; i < header.nr_entries; i++)
	{
		fread((unsigned long*)&header.entry_offset[i],sizeof(unsigned long),1,fp);
		header.entry_offset[i] = htonl(header.entry_offset[i]);
	}
	for(i = 0; i < header.nr_entries; i++)
	{
		fseek(fp,header.entry_offset[i],SEEK_SET);
		fread(buffer,sizeof(char),2,fp);//sif code
		if(buffer[0] == 0x02 && buffer[1] == 0x0b)//MVB control
		{
			MVB_CONTROL_FLAG = 1;
			fread((unsigned char*)&mvb_control.bus_id,sizeof(unsigned char),1,fp);
			fread((unsigned char*)&mvb_control.reserverd1,sizeof(unsigned char),1,fp);
			fread((unsigned short*)&mvb_control.device_address,sizeof(unsigned short),1,fp);
			mvb_control.device_address = htons(mvb_control.device_address);
			fread((unsigned char*)&mvb_control.reserverd2,sizeof(unsigned char),1,fp);
			fread((unsigned char*)&mvb_control.t_ignore,sizeof(unsigned char),1,fp);
			fread((unsigned char*)&mvb_control.reserverd3,sizeof(unsigned char),1,fp);
			fread((unsigned char*)&mvb_control.code,sizeof(unsigned char),1,fp);//needs further parsing(bit level)
			//end mvb control
		}
		else if(buffer[0] == 0x02 && buffer[1] == 0x0d)//MVB_Administrator
		{
			MVB_ADMINISTRATOR_FLAG = 1;
			fread((unsigned char*)&mvb_administrator.bus_id,sizeof(unsigned char),1,fp);
			fread((unsigned char*)&mvb_administrator.reserved1,sizeof(unsigned char),1,fp);

			fread((unsigned short*)&mvb_administrator.checkword0,sizeof(unsigned short),1,fp);
			mvb_administrator.checkword0 = htons(mvb_administrator.checkword0);

			fread((unsigned short*)&mvb_administrator.configuration_version,sizeof(unsigned short),1,fp);
			mvb_administrator.configuration_version = htons(mvb_administrator.configuration_version);

			fread((unsigned short*)&mvb_administrator.t_reply_max,sizeof(unsigned short),1,fp);
			mvb_administrator.t_reply_max = htons(mvb_administrator.t_reply_max);

			fread((unsigned short*)&mvb_administrator.macro_cycles,sizeof(unsigned short),1,fp);
			mvb_administrator.macro_cycles = htons(mvb_administrator.macro_cycles);

			fread((unsigned short*)&mvb_administrator.event_poll_strategy,sizeof(unsigned short),1,fp);
			mvb_administrator.event_poll_strategy = htons(mvb_administrator.event_poll_strategy);

			fread((unsigned short*)&mvb_administrator.basic_period,sizeof(unsigned short),1,fp);
			mvb_administrator.basic_period = htons(mvb_administrator.basic_period);

			fread((unsigned short*)&mvb_administrator.macrocycles_per_turn,sizeof(unsigned short),1,fp);
			mvb_administrator.macrocycles_per_turn = htons(mvb_administrator.macrocycles_per_turn);

			fread((unsigned short*)&mvb_administrator.devices_scan_strategy,sizeof(unsigned short),1,fp);
			mvb_administrator.devices_scan_strategy = htons(mvb_administrator.devices_scan_strategy);

			fread((unsigned short*)&mvb_administrator.reserved2,sizeof(unsigned short),1,fp);
			mvb_administrator.reserved2 = htons(mvb_administrator.reserved2);

			fread((unsigned short*)&mvb_administrator.reserved3,sizeof(unsigned short),1,fp);
			mvb_administrator.reserved3 = htons(mvb_administrator.reserved3);

			fread((unsigned short*)&mvb_administrator.reserved4,sizeof(unsigned short),1,fp);
			mvb_administrator.reserved4 = htons(mvb_administrator.reserved4);

			fread((unsigned short*)&mvb_administrator.reserved5,sizeof(unsigned short),1,fp);
			mvb_administrator.reserved5 = htons(mvb_administrator.reserved5);

			fread((unsigned short*)&mvb_administrator.known_devices_list_offset,sizeof(unsigned short),1,fp);
			mvb_administrator.known_devices_list_offset = htons(mvb_administrator.known_devices_list_offset);

			fread((unsigned short*)&mvb_administrator.reserved_list_offset,sizeof(unsigned short),1,fp);
			mvb_administrator.reserved_list_offset = htons(mvb_administrator.reserved_list_offset);

			fread((unsigned short*)&mvb_administrator.periodic_list_offset,sizeof(unsigned short),1,fp);
			mvb_administrator.periodic_list_offset = htons(mvb_administrator.periodic_list_offset);

			fread((unsigned short*)&mvb_administrator.bus_administrators_list_offset,sizeof(unsigned short),1,fp);
			mvb_administrator.bus_administrators_list_offset = htons(mvb_administrator.bus_administrators_list_offset);

			fread((unsigned short*)&mvb_administrator.devices_scan_list_offset,sizeof(unsigned short),1,fp);
			mvb_administrator.devices_scan_list_offset = htons(mvb_administrator.devices_scan_list_offset);

			fread((unsigned short*)&mvb_administrator.end_list_offset,sizeof(unsigned short),1,fp);
			mvb_administrator.end_list_offset = htons(mvb_administrator.end_list_offset);

			offset_diff = mvb_administrator.reserved_list_offset - mvb_administrator.known_devices_list_offset;
			
			mvb_administrator.known_devices_list = (unsigned short*)malloc(offset_diff);
			
			fread((unsigned short*)mvb_administrator.known_devices_list,sizeof(unsigned short),offset_diff/(sizeof(unsigned short)),fp);
			for(j = 0; j < offset_diff/sizeof(unsigned short);j++)
			{
				mvb_administrator.known_devices_list[j] = htons(mvb_administrator.known_devices_list[j]);
			}
			offset_P0  = ftell(fp);//之后的offset从P0算起，P0是相对于文件开头的offset

			fread((unsigned short*)mvb_administrator.cycle_lists_offsets,sizeof(unsigned short),11,fp);
			for(j = 0; j < 11;j++)
			{
				mvb_administrator.cycle_lists_offsets[j] = htons(mvb_administrator.cycle_lists_offsets[j]);
			}

			fread((unsigned short*)mvb_administrator.split_lists_offsets,sizeof(unsigned short),5,fp);
			for(j = 0; j < 5;j++)
			{
				mvb_administrator.split_lists_offsets[j] = htons(mvb_administrator.split_lists_offsets[j]);
			}
			for(j = 0; j < 10; j++)
			{
				mvb_administrator.cycle_lists_size [j] = 0;
				if(mvb_administrator.cycle_lists_offsets[j+1]-mvb_administrator.cycle_lists_offsets[j] > 0)
				{
					offset_diff = mvb_administrator.cycle_lists_offsets[j+1]-mvb_administrator.cycle_lists_offsets[j];
					mvb_administrator.cycle_lists_size [j] = offset_diff/sizeof(unsigned short);
					mvb_administrator.cycle_lists[j] = (unsigned short *)malloc(offset_diff);

					fread((unsigned short*)mvb_administrator.cycle_lists[j],\
						sizeof(unsigned short),offset_diff/sizeof(unsigned short),fp);

					for(k = 0; k < offset_diff/(sizeof(unsigned short));k++)
					{
						mvb_administrator.cycle_lists[j][k] = htons(mvb_administrator.cycle_lists[j][k]);
					}
				}
			}
			mvb_administrator.cycle_lists_size [10] = 0;
			//1024 cycle, 需根据split list offset的第一个判断是否有数据 
			if(mvb_administrator.split_lists_offsets[0] - mvb_administrator.cycle_lists_offsets[10] > 0)
			{
				offset_diff = mvb_administrator.split_lists_offsets[0]-mvb_administrator.cycle_lists_offsets[10];
				mvb_administrator.cycle_lists_size [10] = offset_diff/sizeof(unsigned short);
				mvb_administrator.cycle_lists[10] = (unsigned short *)malloc(offset_diff);

				fread((unsigned short*)mvb_administrator.cycle_lists[10],\
					sizeof(unsigned short),offset_diff/sizeof(unsigned short),fp);

				for(j = 0; j < offset_diff/(sizeof(unsigned short));j++)
				{
					mvb_administrator.cycle_lists[10][j] = htons(mvb_administrator.cycle_lists[10][j]);
				}
			}
			//split list
			for(j = 0; j < 5; j++)
			{
				fseek(fp,offset_P0 + mvb_administrator.split_lists_offsets[j],SEEK_SET);
				switch (j)
				{
				case 0:
					for(k = 0; k < 4; k++)
					{
						fread((unsigned char*)&mvb_administrator.split_2[k],sizeof(unsigned char),1,fp);
						fread((unsigned char*)&mvb_administrator.split_4[k],sizeof(unsigned char),1,fp);
					}
					break;
				case 1:
					for(k = 0; k < 16; k++)
					{
						fread((unsigned char*)&mvb_administrator.split_8[k],sizeof(unsigned char),1,fp);
						fread((unsigned char*)&mvb_administrator.split_16[k],sizeof(unsigned char),1,fp);
					}
					break;
				case 2:
					for(k = 0; k < 64; k++)
					{
						fread((unsigned char*)&mvb_administrator.split_32[k],sizeof(unsigned char),1,fp);
						fread((unsigned char*)&mvb_administrator.split_64[k],sizeof(unsigned char),1,fp);
					}
					break;
				case 3:
					for(k = 0; k < 256; k++)
					{
						fread((unsigned char*)&mvb_administrator.split_128[k],sizeof(unsigned char),1,fp);
						fread((unsigned char*)&mvb_administrator.split_256[k],sizeof(unsigned char),1,fp);
					}
					break;
				case 4:
					for(k = 0; k < 1024; k++)
					{
						fread((unsigned char*)&mvb_administrator.split_512[k],sizeof(unsigned char),1,fp);
						fread((unsigned char*)&mvb_administrator.split_1024[k],sizeof(unsigned char),1,fp);
					}
					break;
				}
			}
			//bus administrator list
			offset_diff = mvb_administrator.devices_scan_list_offset - mvb_administrator.bus_administrators_list_offset;
			mvb_administrator.bus_administrators_list = (unsigned short*)malloc(offset_diff);
			fread((unsigned short*)mvb_administrator.bus_administrators_list,sizeof(unsigned short),offset_diff/sizeof(unsigned short),fp);
			for(j = 0; j < offset_diff/(sizeof(unsigned short)); j++)
			{
				mvb_administrator.bus_administrators_list[j] = htons(mvb_administrator.bus_administrators_list[j]);
			}
			//device scan list
			mvb_administrator.device_scan_list_count0 = (unsigned char*)malloc(mvb_administrator.macro_cycles/2);
			mvb_administrator.device_scan_list_count1 = (unsigned char*)malloc(mvb_administrator.macro_cycles/2);
			for(j = 0; j < mvb_administrator.macro_cycles/2; j++)
			{
				fread((unsigned char*)&mvb_administrator.device_scan_list_count0[j],sizeof(unsigned char),1,fp);
				fread((unsigned char*)&mvb_administrator.device_scan_list_count1[j],sizeof(unsigned char),1,fp);
			}
			//end mvb administrator

		}
		else if(buffer[0] == 0x02 && buffer[1] == 0x1f)//ports configuration
		{
			PORTS_CONFIGURATION_FLAG = 1;
			fread((unsigned short*)&ports_configuration.nr_ports,sizeof(unsigned short),1,fp);
			ports_configuration.nr_ports = htons(ports_configuration.nr_ports);
			ports_configuration.ports_info_0 = (unsigned short*)malloc(ports_configuration.nr_ports*sizeof(unsigned short));
			ports_configuration.ports_info_1 = (unsigned short*)malloc(ports_configuration.nr_ports*sizeof(unsigned short));

			for(j = 0; j < ports_configuration.nr_ports;j++)
			{
				fread((unsigned short*)&ports_configuration.ports_info_0[j],sizeof(unsigned short),1,fp);//needs further parse
				fread((unsigned short*)&ports_configuration.ports_info_1[j],sizeof(unsigned short),1,fp);//needs further parse
				ports_configuration.ports_info_0[j] = htons(ports_configuration.ports_info_0[j]);
				ports_configuration.ports_info_1[j] = htons(ports_configuration.ports_info_1[j]);
			}
			//end ports configuration
		}
		else if(buffer[0] == 0x02 && buffer[1] == 0x28)//md control
		{
			MD_CONTROL_FLAG = 1;
			fread((unsigned short*)&md_control.max_call_number,sizeof(unsigned short),1,fp);
			md_control.max_call_number = htons(md_control.max_call_number);
			fread((unsigned short*)&md_control.max_inst_number,sizeof(unsigned short),1,fp);
			md_control.max_inst_number = htons(md_control.max_inst_number);
			fread((unsigned short*)&md_control.default_reply_timeout,sizeof(unsigned short),1,fp);
			md_control.default_reply_timeout = htons(md_control.default_reply_timeout);
			fread((unsigned char*)&md_control.reserverd1,sizeof(unsigned char),1,fp);
			fread((unsigned char*)&md_control.my_credit,sizeof(unsigned char),1,fp);
			//end md control

		}
		else if(buffer[0] == 0x02 && buffer[1] == 0x2b)//Function_Directory
		{
			FUNCTION_DIRECTORY_FLAG = 1;
			fread((unsigned char*)&function_directory.clear_directory,sizeof(unsigned char),1,fp);
			fread((unsigned char*)&function_directory.nr_functions,sizeof(unsigned char),1,fp);
			function_directory.function_id = (unsigned char*)malloc(function_directory.nr_functions);
			function_directory.station_id = (unsigned char*)malloc(function_directory.nr_functions);

			for(j = 0;  j < function_directory.nr_functions; j++)
			{
				fread((unsigned char*)&function_directory.function_id[j],sizeof(unsigned char),1,fp);
				fread((unsigned char*)&function_directory.station_id[j],sizeof(unsigned char),1,fp);
 			}
			//end Function_Directory
		}
		else//should never be here
		{
			//char * error = (char *)malloc(32);
			//sprintf(error,"Bin file error, not correct sif code:%x, %x",buffer[0],buffer[1]);
			printf("Bin file error, not correct sif code: 0x%02x,0x%02x",buffer[0],buffer[1]);
			return 0;
		}

	}
	fclose(fp);
	//////////////////////////////////////////////////////////////////////////
	/************************************************************************/
	/* main_frame                                                           */
	/************************************************************************/
	if(MVB_ADMINISTRATOR_FLAG)
	{
		main_frame = (unsigned short*)malloc(sizeof(unsigned short)*1024*8);
		cursor = (unsigned short*)malloc(sizeof(unsigned short)*1024);
		array = (unsigned short*)malloc(sizeof(unsigned short)*1024);
		memset(main_frame,0,sizeof(unsigned short)*1024*8);
		memset(cursor,0,sizeof(unsigned short)*1024);
		memset(array,0,sizeof(unsigned short)*1024);
		for(i = 0; i < 1024; i++)
		{
			cursor [i] = 0;
		}
		for(i = 1 ; i < 11; i++)
		{
			switch (i)
			{
				case 1:
					for(j = 0; j < power [i]; j++)
					{
						array [j] = mvb_administrator.split_2[j];
					}
					break;
				case 2:
					for(j = 0; j < power [i]; j++)
					{
						array [j] = mvb_administrator.split_4[j];
					}
					break;
				case 3:
					for(j = 0; j < power [i]; j++)
					{
						array [j] = mvb_administrator.split_8[j];
					}
					break;
				case 4:
					for(j = 0; j < power [i]; j++)
					{
						array [j] = mvb_administrator.split_16[j];
					}
					break;
				case 5:
					for(j = 0; j < power [i]; j++)
					{
						array [j] = mvb_administrator.split_32[j];
					}
					break;
				case 6:
					for(j = 0; j < power [i]; j++)
					{
						array [j] = mvb_administrator.split_64[j];
					}
					break;
				case 7:
					for(j = 0; j < power [i]; j++)
					{
						array [j] = mvb_administrator.split_128[j];
					}
					break;
				case 8:
					for(j = 0; j < power [i]; j++)
					{
						array [j] = mvb_administrator.split_256[j];
					}
					break;
				case 9:
					for(j = 0; j < power [i]; j++)
					{
						array [j] = mvb_administrator.split_512[j];
					}
					break;
				case 10:
					for(j = 0; j < power [i]; j++)
					{
						array [j] = mvb_administrator.split_1024[j];
					}
					break;
			}

			sum = 0;
			for(j = 0; j < power [i]; j++)
			{
				if(array [j] != 0)
				{
					for(count = 0; count < array [j]; count++)
					{
						for(k = 0; k < 1024; k++)
						{
							if((k-j) % power [i] == 0)
							{
								main_frame[k*8+cursor[k]] = mvb_administrator.cycle_lists [i][sum];
								cursor [k]++;
							}

						}
						sum++;
					}
				}
			}

		}//end main frame
		free(cursor);
		free(array);
	}

	
#endif // ifndef MVBPROJ_INIT_BIN_BLOCKED

#ifdef MVBPROJ_DEFAULT_ADDRESS
	mvb_control.device_address = MVBPROJ_DEFAULT_ADDRESS;
#ifdef MVBPROJ_BASIC_INFO_SUPPORT
	printf("Binary init :: DEFAULT ADDRESS :: 0x%04x\n", mvb_control.device_address);
#endif // ifdef MVBPROJ_BASIC_INFO_SUPPORT
#endif // ifdef MVBPROJ_DEFAULT_ADDRESS


#ifndef MVBPROJ_INIT_BIN_TRANS_BLOCKED

	if(MVB_CONTROL_FLAG)
	{
		data = 0;
		data2 = 0;
		switch(mvb_control.code & LINE_MASK)
		{
			case 0x0C:
				data |= 0xC000; 
				break;
			case 0x08:
				data |= 0x8000;
				break;
			case 0x04:
				data |= 0x4000;
				break;
		}
		if(mvb_control.code & BA_MASK)
		{
			data |= 0x2000;
		}
		data |= mvb_control.device_address;
		data2 = data;
		data2 &= 0x0000FFFF;

#ifdef MVBPROJ_BASIC_INFO_SUPPORT
	printf("Binary init :: MVB CONTROL :: 0x%04x\n", data2);
#endif // ifdef MVBPROJ_BASIC_INFO_SUPPORT

		HAL_IO_OUTPUT(data2);
		HAL_IO_INIT_OUTPUT_PULSE;
	}


	if (MVB_ADMINISTRATOR_FLAG)
	{
#ifdef MVBPROJ_BASIC_INFO_SUPPORT
#if !defined(MVBPROJ_DEFAULT_EMPTY_MAINFRAME)
	printf("Binary init :: MVB ADMINISTRATOR :: 8192 main frame words\n");
#else
	printf("Binary init :: MVB ADMINISTRATOR :: 8192 empty words\n");
#endif // if !defined(MVBPROJ_DEFAULT_EMPTY_MAINFRAME)
#endif // ifdef MVBPROJ_BASIC_INFO_SUPPORT

		for(i = 0; i < 8192;i++)
		{
			//mvb_arm_delay(0xFF);
			data2 = main_frame [i] & 0x0000FFFF;
			//data = htonl(data);
			
#ifdef MVBPROJ_DEFAULT_EMPTY_MAINFRAME
			data2 = 0;
#endif // ifdef MVBPROJ_DEFAULT_EMPTY_MAINFRAME

			HAL_IO_OUTPUT(data2);
			HAL_IO_INIT_OUTPUT_PULSE;
			//printf("0x%08x",data);
		}
		free(main_frame);
	}
	else
	{
#ifdef MVBPROJ_BASIC_INFO_SUPPORT
	printf("Binary init :: MVB ADMINISTRATOR :: 8192 empty words\n");
#endif // ifdef MVBPROJ_BASIC_INFO_SUPPORT
		for(i = 0; i < 8192;i++)
		{
			data2 = 0;
			//data = htonl(data);
			HAL_IO_OUTPUT(data2);
			HAL_IO_INIT_OUTPUT_PULSE;
			//printf("0x%08x",data);
		}
	}
	
	if(PORTS_CONFIGURATION_FLAG)
	{
#ifdef MVBPROJ_BASIC_INFO_SUPPORT
#if !defined(MVBPROJ_DEFAULT_EMPTY_PORTCONFIG)
	printf("Binary init :: PORTS CONFIGURATION :: 4096 words\n");
#else
	printf("Binary init :: PORTS CONFIGURATION :: 4096 empty words\n");
#endif // if !defined(MVBPROJ_DEFAULT_EMPTY_PORTCONFIG)
#endif // ifdef MVBPROJ_BASIC_INFO_SUPPORT
		for(i = 0; i < 4096; i++)
		{
			data = 0;
			data2 = 0;
			for(j = 0; j < ports_configuration.nr_ports; j++)
			{
				if(ports_configuration.ports_info_0[j] == i)
				{
					if(ports_configuration.ports_info_1[j] & SRC_MASK)//source
					{
						data |= 0x8000;
					}
					data |= ports_configuration.ports_info_1[j] & FCODE_MASK;
					data |= ports_configuration.ports_info_0[j] & PORTADDRESS_MASK;
					break;
				}
			}
			data2 = data;
			data2 &= 0x0000FFFF;

#ifdef MVBPROJ_DEFAULT_EMPTY_PORTCONFIG
			data2 = 0;
#endif // ifdef MVBPROJ_DEFAULT_EMPTY_PORTCONFIG
			HAL_IO_OUTPUT(data2);
			HAL_IO_INIT_OUTPUT_PULSE;
		}
	}

	HAL_IO_INIT_FINISH;
	
#endif // ifndef MVBPROJ_INIT_BIN_TRANS_BLOCKED

	return 1;


}

/* --------------------------------------------------------------------------
 *  create_structure
 *
 *  Data structure creation
 *
 *  @param	: void
 *  @return	: void
 *
 *  Create data structure:
 *    01. Device status (struct)
 *    02. Device status (UNSIGNED16)
 *    03. Devices list (address less than BA_ADMIN_BAL_SIZE)
 *    04. Devices list timeout count (address less than BA_ADMIN_BAL_SIZE)
 *    05. Known devices list
 * --------------------------------------------------------------------------
 */
void create_structure()
{
	this_akey = mvb_administrator.configuration_version;
	this_addr = mvb_control.device_address;
	
	mvb_device_status.ser = 0;
	mvb_device_status.dnr = 0;
	mvb_device_status.frc = 0;
	mvb_device_status.erd = 0;
	mvb_device_status.sdd = 0;
	mvb_device_status.ssd = 0;
	mvb_device_status.rld = 0;
	mvb_device_status.lat = 0;
	
	mvb_device_status.cs3 = 0;
	mvb_device_status.cs2 = 0;
	mvb_device_status.cs1 = this_akey % 2;
	mvb_device_status.cs0 = (this_akey >> 1) % 2;
	
	mvb_device_status.md = 0;
	mvb_device_status.gw = 0;
	mvb_device_status.ba = 0;
	mvb_device_status.sp = 0;

	if (FUNCTION_DIRECTORY_FLAG)
	{
		mvb_device_status.md = 1;
	}
	
	if (MVB_ADMINISTRATOR_FLAG)
	{
		mvb_device_status.ba = 1;
		mvb_device_status.cs2 = 1;
	}
	
#ifdef MVBPROJ_ROLE_MASTER
	mvb_device_status.ba = 1;
	mvb_device_status.cs2 = 1;
#endif // ifdef MVBPROJ_ROLE_MASTER

#ifdef MVBPROJ_ROLE_SLAVE
	mvb_device_status.ba = 0;
	mvb_device_status.cs2 = 0;
#endif // ifdef MVBPROJ_ROLE_SLAVE
	
	
	mvb_device_status_16 = *((cyg_uint16*)&mvb_device_status);
	ba_structure();

#ifdef MVBPROJ_DEFAULT_DEVICES_SCAN_STRATEGY
	mvb_administrator.devices_scan_strategy = MVBPROJ_DEFAULT_DEVICES_SCAN_STRATEGY;
#ifdef MVBPROJ_DEBUG_INFO
	printf("[INIT] Devices scan default strategy loaded.\n");
#endif
#endif // ifdef MVBPROJ_DEFAULT_DEVICES_SCAN_STRATEGY
	
#ifdef MVBPROJ_DEFAULT_MASTER_ADDRESS
	if (this_addr == MVBPROJ_DEFAULT_MASTER_ADDRESS)
	{
		ba_init(false);
#ifdef MVBPROJ_DEBUG_INFO
		printf("[INIT] Default master, current mas = 1.\n");
#endif
	}
#endif // ifdef MVBPROJ_DEFAULT_MASTER_ADDRESS

#ifdef MVBPROJ_DEFAULT_KDL_V1
	mvb_administrator.known_devices_list = (unsigned short*)malloc(1);
	mvb_administrator.known_devices_list[0] = 0x01;
	mvb_administrator.known_devices_list_offset = 0;
	mvb_administrator.reserved_list_offset = 2;
#ifdef MVBPROJ_DEBUG_INFO
	printf("[INIT] Default KDL Version.1 : 0x30.\n");
#endif // ifdef MVBPROJ_DEBUG_INFO
#endif // ifdef MVBPROJ_DEFAULT_KDL_V1

#ifdef MVBPROJ_DEFAULT_KDL_V2
	mvb_administrator.known_devices_list = (unsigned short*)malloc(2);
	mvb_administrator.known_devices_list[0] = 0x01;
	mvb_administrator.known_devices_list[1] = 0x81;
	mvb_administrator.known_devices_list_offset = 0;
	mvb_administrator.reserved_list_offset = 4;
#ifdef MVBPROJ_DEBUG_INFO
	printf("[INIT] Default KDL Version.2 : 0x30, 0x40.\n");
#endif // ifdef MVBPROJ_DEBUG_INFO
#endif // ifdef MVBPROJ_DEFAULT_KDL_V2

#ifdef MVBPROJ_DEFAULT_KDL_V3
	mvb_administrator.known_devices_list = (unsigned short*)malloc(5);
	mvb_administrator.known_devices_list[0] = 0x20;
	mvb_administrator.known_devices_list[1] = 0x10;
	mvb_administrator.known_devices_list[2] = 0x81;
	mvb_administrator.known_devices_list[3] = 0x01;
	mvb_administrator.known_devices_list[4] = 0x30;
	mvb_administrator.known_devices_list_offset = 0;
	mvb_administrator.reserved_list_offset = 10;
#ifdef MVBPROJ_DEBUG_INFO
	printf("[INIT] Default KDL Version.3 : 0x01, 0x40, 0x46.\n");
#endif // ifdef MVBPROJ_DEBUG_INFO
#endif // ifdef MVBPROJ_DEFAULT_KDL_V3

#ifdef MVBPROJ_DEBUG_INFO
	printf("[INIT] Create data structure completed.\n");
	printf("[INIT] Address: 0x%04x\n", this_addr);
	printf("[INIT] Status: 0x%04x\n", mvb_device_status_16);
#endif

}