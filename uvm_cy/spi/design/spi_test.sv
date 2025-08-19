class spi_test extends uvm_test;
  `uvm_component_utils(spi_test)

  spi_env env;
  spi_seq seq;
  
  int seq_count = 10;
 

	 function new(string name, uvm_component parent);
    		super.new(name, parent);
 	 endfunction

  	function void build_phase(uvm_phase phase);
    		super.build_phase(phase);
    		env = spi_env::type_id::create("env", this);
  	endfunction

 	 task run_phase(uvm_phase phase);
    		seq = spi_seq::type_id::create("seq");

    		seq.seq_count = this.seq_count;
   		`uvm_info("TEST", $sformatf("Starting sequences with config:\n\
                                Normal: count=%0d ",
                                seq.seq_count),
                                UVM_MEDIUM)

  phase.raise_objection(this);
      seq.start(env.agt.sqr);
    wait(env.scb.tran_index - 1 == seq.seq_count);
//	#10000;
    phase.drop_objection(this);
  endtask
endclass
