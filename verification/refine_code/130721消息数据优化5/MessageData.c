#include "MessageData.h"

#ifdef MVBPROJ_DEBUG_INFO
#include <stdio.h>
#endif

extern UNSIGNED16 this_addr;
extern MVB_DEVICE_STATUS mvb_device_status;

extern UNSIGNED16 current_mf;
extern UNSIGNED16 current_sf;
extern UNSIGNED16 ba_mf;

UNSIGNED16 current_index = 0;
/*****************************************/
/*************Master Slave****************/
/*****************************************/


void bsp_handler()
{
//diag_printf( "bsp\n" );
	if( !md_notime )
	{
		last_address = md_get_next(last_address);
		if( last_address == 0 )
			last_address = md_get_next(last_address);
		if( !md_notime )
			send_read_request( last_address );
	}
}
void slaveframe_handler()
{
//diag_printf( "slaveframe\n" );
	if( !md_notime )
	{
		last_address = md_get_next(last_address);
		if( last_address == 0 )
			last_address = md_get_next(last_address);
		if( !md_notime )
			send_read_request( last_address );
	}
}
void timeout_handler()
{
//diag_printf( "timeout\n" );
	if( !md_notime )
	{
		last_address = md_get_next(last_address);
		if( last_address == 0 )
			last_address = md_get_next(last_address);
		if( !md_notime )
			send_read_request( last_address );
	}
}
void collision_handler()
{
//diag_printf( "collision\n" );
	if( !md_notime )
	{
		last_address = md_get_next(last_address);
		if( last_address == 0 )
			last_address = md_get_next(last_address);
		if( !md_notime )
			send_read_request( last_address );
	}
}

void Fcode_9_handler()
{
//diag_printf( "9" );
	cyg_uint32 uart_checkbit;
	HAL_IO_UART_CHECKBIT(&uart_checkbit);
    if ( uart_checkbit == HAL_IO_ENUM_UART_NOT_EMPTY )
    {
        //发送响应从帧
        event_identifier_response();
    }
}

void Fcode_13_handler()
{
//diag_printf( "13" );
    //判断标志位，如果本次参与仲裁，就发送响应从帧，否则不做处理
	cyg_uint32 uart_checkbit;
	HAL_IO_UART_CHECKBIT(&uart_checkbit);
    if ( uart_checkbit == HAL_IO_ENUM_UART_NOT_EMPTY )
    {
        if( match_group_address() )
            event_identifier_response();
    }
}

void Fcode_14_handler()
{
//diag_printf( "14" );
    //判断标志位，如果本次参与仲裁，就发送响应从帧，否则不做处理
	cyg_uint32 uart_checkbit;
	HAL_IO_UART_CHECKBIT(&uart_checkbit);
    if ( uart_checkbit == HAL_IO_ENUM_UART_NOT_EMPTY )
    {
        if( match_device_address() )
            event_identifier_response();
    }
}

void Fcode_12_handler()
{
//diag_printf( "12" );
	//last_addr = current_mf & address_filter;
	cyg_uint32 uart_checkbit;
	HAL_IO_UART_CHECKBIT(&uart_checkbit);
    if ( uart_checkbit == HAL_IO_ENUM_UART_NOT_EMPTY && is_source() )
	{
        mvb_arm_send_message();
		
    }
}

/********************************************/
/**************HardwareInterface*************/
/********************************************/

int send_general_request( void )
{
    mvb_arm_send_main_frame( 0x9110 );
}

int send_group_request( int M , int C )
{
    UNSIGNED16 frame = 0xD000;
    UNSIGNED16 tmp = 0x0000;
    int count = 0 ;
    for( count = 0 ; count < M ; ++count )
    {
        tmp += 1;
        tmp <<= 1;
    }
    tmp <<= ( 12 - M );
	frame += tmp;
    frame += C;
    mvb_arm_send_main_frame( frame );
}

int send_single_request( int C )
{
    mvb_arm_send_main_frame( 0xE000 + C );
}

int send_read_request( UNSIGNED16 device_address )
{
    mvb_arm_send_main_frame( 0xC000 + device_address );
}

int event_identifier_response()
{
#ifdef MVBPROJ_DEBUG_INFO
    printf( "send slave frame %x\n" , 0xC000 + this_addr );
#endif
	mvb_arm_send_slave_frame( 0xC000 + this_addr );
}

int match_group_address()
{
    UNSIGNED16 device_address_tmp = current_mf & address_filter ;
	int i = 0 ;
    for( i = 0 ; i < 12 ; ++i )
    {
        if( ( device_address_tmp & group_filter[i] ) == 0 )
            break;
    }
    last_M = i + 1;
    last_C = device_address_tmp << ( last_M + 4 );
    last_C >>= ( last_M + 4 );

    int C_tmp = this_addr << ( last_M + 4 );
    C_tmp >>= ( last_M + 4 );
    if( last_C == C_tmp )
        return 1;
    return 0;
}
