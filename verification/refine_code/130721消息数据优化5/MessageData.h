#include "mvb_project.h"
#include "mvb_def.h"
#include "hal.h"

#define md_get_pre(address)  ( ( md_ability_array[address].pre_high << 8 )  + md_ability_array[address].pre_low )
#define md_get_next(address) ( ( md_ability_array[address].next_high << 8 ) + md_ability_array[address].next_low )
#define md_set_pre( address , value ) 	{\
											md_ability_array[address].pre_high = ( value >> 8 );\
											md_ability_array[address].pre_low = ( value & 0xff);\
										}
#define md_set_next( address , value )	{\
											md_ability_array[address].next_high = ( value >> 8 );\
											md_ability_array[address].next_low = ( value & 0xff);\
										}

struct MD_ABILITY_NODE
{
	UNSIGNED8 pre_high:4;
	UNSIGNED8 next_high:4;
	UNSIGNED8 pre_low:8;
	UNSIGNED8 next_low:8;
	
};
struct MD_ABILITY_NODE md_ability_array[4096]={{0,0,0,0}};
UNSIGNED8 md_ability_count = 0 ;

/********************************************/
/****************HardwareInterface***********/
/********************************************/
#define address_filter 0x0FFF
#define fcode_filter 0xF000

UNSIGNED16 last_M;//group_address中的M
UNSIGNED16 last_C;//group_address中的C
UNSIGNED16 last_address = 0;
int md_notime = 0;

UNSIGNED16 group_filter[12] ={ 0x0800 , 0x0400 , 0x0200 , 0x0100 , 0x0080 , 0x0040 , 0x0020 , 0x0010 , 0x0008 , 0x0004 , 0x0002 , 0x0001 };//组地址解析需要的mask

//发送General_Event_Request主帧
//F_code = 9 ; Event_Mode = answer_now , new_round ; ET = high_priority ;
//0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15
//1|0|0|1|0|0|0|1|0|0| 0| 0| 0| 0| 0| 0
//**************************************
//发送成功 ，返回SUCCESS
//发送失败 ，返回FAIL
//剩余时间不足 ，返回NOTIME
int send_general_request( void );

//发送Group_Event_Request主帧
//F_code = 13; mask = M 中 1 的个数减一 后 加一个0 ; Group_Address 为C的2进制表示
//0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15
//1|1|0|1|1|1|1|1|1|0| A| B| C| D| E| F
//**************************************
//发送成功 ，返回SUCCESS
//发送失败 ，返回FAIL
//剩余时间不足 ， 返回NOTIME
int send_group_request( int M , int C );

//发送Group_Event_Request主帧
//F_code = 14; Device_Address 为C的2进制表示
//0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15
//1|1|0|0|A|A|A|A|A|A| A| A| A| A| A| A
//**************************************
//发送成功 ，返回SUCCESS
//发送失败 ，返回FAIL
//剩余时间不足 ， 返回NOTIME
int send_single_request( int C );


//发送Event_Read_Request主帧
//F_code = 12 ; Device Address
//0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15
//1|1|0|0|A|A|A|A|A|A| A| A| A| A| A| A
//*************************************
//消息数据从帧发生冲突 ，返回COLLISION
//消息数据从帧超时，返回TIMEOUT
//消息数据从帧发送成功，返回SUCCESS
int send_read_request( UNSIGNED16 device_address );

//响应从设备对主设备仲裁帧
//F_code = 12 ; Device Address
//0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15
//1|1|0|0|A|A|A|A|A|A| A| A| A| A| A| A
//*************************************
//发送成功 ，返回SUCCESS
//发送失败 ，返回FAIL
int event_identifier_response();

//从设备接收到主帧f_code = 12 后，判断在主帧中中的设备地址本机设备
//***********************************
//主帧中设备地址和本机设备地址相同，返回1
//否则，返回0
#define is_source() (this_addr == ( current_mf & address_filter ))

//判断当前接收的Single_Event_Request主帧中的设备地址是不是与本机地址相同
//***********************************
//如果相同 ，返回1
//否则 ，返回0
#define match_device_address() ( ( this_addr == ( current_mf & address_filter ) ) && ( ( ( current_mf & fcode_filter ) >> 12 )== 14 ) )

//判断本机地址是不是属于当前接收的Group_Event_Request主帧中的组地址
//***********************************
//如果属于主帧中的组地址 ，返回1
//否则 ，返回0
int match_group_address();

//bap中断处理函数
void bsp_handler();

//slaveframe中断处理函数
void slaveframe_handler();

//timeout中断处理函数
void timeout_handler();

//collision中断处理函数
void collision_handler();

//对masterframe中断的Fcode9的处理函数
void Fcode_9_handler();

//对masterframe中断的Fcode13的处理函数
void Fcode_13_handler();

//对masterframe中断的Fcode14的处理函数
void Fcode_14_handler();

//对masterframe中断的Fcode12的处理函数
void Fcode_12_handler();
