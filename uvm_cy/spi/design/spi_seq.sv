//Seq is a components that generate 1 or more transaction and control order.
//It is sit above sequencer.
//Act as stimuli brain

class spi_seq extends uvm_sequence#(spi_tran);
	`uvm_object_utils(spi_seq)

 	int seq_count;
	int seq_index;

  function new(string name = "spi_seq");
    super.new(name);
    seq_index = 0;
   // seq_type = "normal";
  endfunction

	task body();
		spi_tran tr;
		`uvm_info(get_type_name(), "Normal Priority Sequence", UVM_MEDIUM)
		repeat(seq_count) begin 
			tr=spi_tran::type_id::create("tr");
			start_item(tr);
			assert(tr.randomize());
			seq_index++;
			tr.seq_count = this.seq_count;
			tr.seq_index = this.seq_index;
		//	tr.seq_type = this.seq_type;

			finish_item(tr);
`uvm_info(get_type_name(), $sformatf("Sent %0d/%0d ---------------start=%0b, busy=%0b, done=%0b , tx_data=0x%8b rx_data=0x%8b, MOSI=0x%8b, MISO=0x%8b ",
                                           seq_index, seq_count,  tr.start, tr.busy , tr.done , tr.tx_data, tr.rx_data,tr.mosi,tr.miso ),
                                           UVM_MEDIUM)
		end
	endtask
endclass
			



 
