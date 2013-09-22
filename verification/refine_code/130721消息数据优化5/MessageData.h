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

UNSIGNED16 last_M;//group_address�е�M
UNSIGNED16 last_C;//group_address�е�C
UNSIGNED16 last_address = 0;
int md_notime = 0;

UNSIGNED16 group_filter[12] ={ 0x0800 , 0x0400 , 0x0200 , 0x0100 , 0x0080 , 0x0040 , 0x0020 , 0x0010 , 0x0008 , 0x0004 , 0x0002 , 0x0001 };//���ַ������Ҫ��mask

//����General_Event_Request��֡
//F_code = 9 ; Event_Mode = answer_now , new_round ; ET = high_priority ;
//0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15
//1|0|0|1|0|0|0|1|0|0| 0| 0| 0| 0| 0| 0
//**************************************
//���ͳɹ� ������SUCCESS
//����ʧ�� ������FAIL
//ʣ��ʱ�䲻�� ������NOTIME
int send_general_request( void );

//����Group_Event_Request��֡
//F_code = 13; mask = M �� 1 �ĸ�����һ �� ��һ��0 ; Group_Address ΪC��2���Ʊ�ʾ
//0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15
//1|1|0|1|1|1|1|1|1|0| A| B| C| D| E| F
//**************************************
//���ͳɹ� ������SUCCESS
//����ʧ�� ������FAIL
//ʣ��ʱ�䲻�� �� ����NOTIME
int send_group_request( int M , int C );

//����Group_Event_Request��֡
//F_code = 14; Device_Address ΪC��2���Ʊ�ʾ
//0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15
//1|1|0|0|A|A|A|A|A|A| A| A| A| A| A| A
//**************************************
//���ͳɹ� ������SUCCESS
//����ʧ�� ������FAIL
//ʣ��ʱ�䲻�� �� ����NOTIME
int send_single_request( int C );


//����Event_Read_Request��֡
//F_code = 12 ; Device Address
//0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15
//1|1|0|0|A|A|A|A|A|A| A| A| A| A| A| A
//*************************************
//��Ϣ���ݴ�֡������ͻ ������COLLISION
//��Ϣ���ݴ�֡��ʱ������TIMEOUT
//��Ϣ���ݴ�֡���ͳɹ�������SUCCESS
int send_read_request( UNSIGNED16 device_address );

//��Ӧ���豸�����豸�ٲ�֡
//F_code = 12 ; Device Address
//0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15
//1|1|0|0|A|A|A|A|A|A| A| A| A| A| A| A
//*************************************
//���ͳɹ� ������SUCCESS
//����ʧ�� ������FAIL
int event_identifier_response();

//���豸���յ���֡f_code = 12 ���ж�����֡���е��豸��ַ�����豸
//***********************************
//��֡���豸��ַ�ͱ����豸��ַ��ͬ������1
//���򣬷���0
#define is_source() (this_addr == ( current_mf & address_filter ))

//�жϵ�ǰ���յ�Single_Event_Request��֡�е��豸��ַ�ǲ����뱾����ַ��ͬ
//***********************************
//�����ͬ ������1
//���� ������0
#define match_device_address() ( ( this_addr == ( current_mf & address_filter ) ) && ( ( ( current_mf & fcode_filter ) >> 12 )== 14 ) )

//�жϱ�����ַ�ǲ������ڵ�ǰ���յ�Group_Event_Request��֡�е����ַ
//***********************************
//���������֡�е����ַ ������1
//���� ������0
int match_group_address();

//bap�жϴ�����
void bsp_handler();

//slaveframe�жϴ�����
void slaveframe_handler();

//timeout�жϴ�����
void timeout_handler();

//collision�жϴ�����
void collision_handler();

//��masterframe�жϵ�Fcode9�Ĵ�����
void Fcode_9_handler();

//��masterframe�жϵ�Fcode13�Ĵ�����
void Fcode_13_handler();

//��masterframe�жϵ�Fcode14�Ĵ�����
void Fcode_14_handler();

//��masterframe�жϵ�Fcode12�Ĵ�����
void Fcode_12_handler();
